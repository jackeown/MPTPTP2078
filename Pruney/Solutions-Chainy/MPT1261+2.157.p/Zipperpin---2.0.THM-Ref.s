%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9jVnGvPdvj

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:02 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 475 expanded)
%              Number of leaves         :   42 ( 156 expanded)
%              Depth                    :   18
%              Number of atoms          : 1461 (5324 expanded)
%              Number of equality atoms :  108 ( 343 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t77_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k2_tops_1 @ X40 @ X39 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X40 ) @ ( k2_pre_topc @ X40 @ X39 ) @ ( k1_tops_1 @ X40 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( ( k2_pre_topc @ X42 @ X41 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X42 ) @ X41 @ ( k2_tops_1 @ X42 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('16',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X44 @ X43 ) @ X43 )
      | ~ ( v4_pre_topc @ X43 @ X44 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('24',plain,(
    ! [X31: $i,X33: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( r1_tarski @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) )
      | ( ( k4_subset_1 @ X25 @ X24 @ X26 )
        = ( k2_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('32',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('35',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('36',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X23 @ ( k3_subset_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('41',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','42'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('44',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X21 ) @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('45',plain,(
    ! [X18: $i] :
      ( ( k2_subset_1 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('46',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','56'])).

thf('58',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['34','57'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('60',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('62',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('63',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('65',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('70',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['60','71'])).

thf('73',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['29','72'])).

thf('74',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','73'])).

thf('75',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['75'])).

thf('77',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('78',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('80',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( ( k7_subset_1 @ X28 @ X27 @ X29 )
        = ( k4_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('83',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('85',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['78','87'])).

thf('89',plain,(
    ! [X31: $i,X33: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( r1_tarski @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('90',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('92',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('94',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('95',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('97',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','56'])).

thf('99',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('101',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('103',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['92','103'])).

thf('105',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['77','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('107',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X37 @ X38 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('108',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['105','111'])).

thf('113',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['75'])).

thf('114',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('116',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['76','114','115'])).

thf('117',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['74','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('119',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','117','118'])).

thf('120',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['75'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('122',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['76','114'])).

thf('124',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['122','123'])).

thf('125',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['119','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9jVnGvPdvj
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:06:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.66/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.66/0.85  % Solved by: fo/fo7.sh
% 0.66/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.85  % done 1469 iterations in 0.412s
% 0.66/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.66/0.85  % SZS output start Refutation
% 0.66/0.85  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.66/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.66/0.85  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.66/0.85  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.66/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.85  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.66/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.66/0.85  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.66/0.85  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.66/0.85  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.66/0.85  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.66/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.85  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.66/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.66/0.85  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.66/0.85  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.66/0.85  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.66/0.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.66/0.85  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.66/0.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.66/0.85  thf(t77_tops_1, conjecture,
% 0.66/0.85    (![A:$i]:
% 0.66/0.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.85       ( ![B:$i]:
% 0.66/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.85           ( ( v4_pre_topc @ B @ A ) <=>
% 0.66/0.85             ( ( k2_tops_1 @ A @ B ) =
% 0.66/0.85               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.66/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.85    (~( ![A:$i]:
% 0.66/0.85        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.85          ( ![B:$i]:
% 0.66/0.85            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.85              ( ( v4_pre_topc @ B @ A ) <=>
% 0.66/0.85                ( ( k2_tops_1 @ A @ B ) =
% 0.66/0.85                  ( k7_subset_1 @
% 0.66/0.85                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.66/0.85    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.66/0.85  thf('0', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(l78_tops_1, axiom,
% 0.66/0.85    (![A:$i]:
% 0.66/0.85     ( ( l1_pre_topc @ A ) =>
% 0.66/0.85       ( ![B:$i]:
% 0.66/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.85           ( ( k2_tops_1 @ A @ B ) =
% 0.66/0.85             ( k7_subset_1 @
% 0.66/0.85               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.66/0.85               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.66/0.85  thf('1', plain,
% 0.66/0.85      (![X39 : $i, X40 : $i]:
% 0.66/0.85         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.66/0.85          | ((k2_tops_1 @ X40 @ X39)
% 0.66/0.85              = (k7_subset_1 @ (u1_struct_0 @ X40) @ 
% 0.66/0.85                 (k2_pre_topc @ X40 @ X39) @ (k1_tops_1 @ X40 @ X39)))
% 0.66/0.85          | ~ (l1_pre_topc @ X40))),
% 0.66/0.85      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.66/0.85  thf('2', plain,
% 0.66/0.85      ((~ (l1_pre_topc @ sk_A)
% 0.66/0.85        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.85            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.85               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.66/0.85      inference('sup-', [status(thm)], ['0', '1'])).
% 0.66/0.85  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('4', plain,
% 0.66/0.85      (((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.85         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.66/0.85            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.66/0.85      inference('demod', [status(thm)], ['2', '3'])).
% 0.66/0.85  thf('5', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(t65_tops_1, axiom,
% 0.66/0.85    (![A:$i]:
% 0.66/0.85     ( ( l1_pre_topc @ A ) =>
% 0.66/0.85       ( ![B:$i]:
% 0.66/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.85           ( ( k2_pre_topc @ A @ B ) =
% 0.66/0.85             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.66/0.85  thf('6', plain,
% 0.66/0.85      (![X41 : $i, X42 : $i]:
% 0.66/0.85         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.66/0.85          | ((k2_pre_topc @ X42 @ X41)
% 0.66/0.85              = (k4_subset_1 @ (u1_struct_0 @ X42) @ X41 @ 
% 0.66/0.85                 (k2_tops_1 @ X42 @ X41)))
% 0.66/0.85          | ~ (l1_pre_topc @ X42))),
% 0.66/0.85      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.66/0.85  thf('7', plain,
% 0.66/0.85      ((~ (l1_pre_topc @ sk_A)
% 0.66/0.85        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.66/0.85            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.85               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.66/0.85      inference('sup-', [status(thm)], ['5', '6'])).
% 0.66/0.85  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('9', plain,
% 0.66/0.85      (((k2_pre_topc @ sk_A @ sk_B)
% 0.66/0.85         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.85            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.66/0.85      inference('demod', [status(thm)], ['7', '8'])).
% 0.66/0.85  thf('10', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(t3_subset, axiom,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.66/0.85  thf('11', plain,
% 0.66/0.85      (![X31 : $i, X32 : $i]:
% 0.66/0.85         ((r1_tarski @ X31 @ X32) | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 0.66/0.85      inference('cnf', [status(esa)], [t3_subset])).
% 0.66/0.85  thf('12', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.66/0.85      inference('sup-', [status(thm)], ['10', '11'])).
% 0.66/0.85  thf('13', plain,
% 0.66/0.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.85          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.85             (k1_tops_1 @ sk_A @ sk_B)))
% 0.66/0.85        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('14', plain,
% 0.66/0.85      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.66/0.85      inference('split', [status(esa)], ['13'])).
% 0.66/0.85  thf('15', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(t69_tops_1, axiom,
% 0.66/0.85    (![A:$i]:
% 0.66/0.85     ( ( l1_pre_topc @ A ) =>
% 0.66/0.85       ( ![B:$i]:
% 0.66/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.85           ( ( v4_pre_topc @ B @ A ) =>
% 0.66/0.85             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.66/0.85  thf('16', plain,
% 0.66/0.85      (![X43 : $i, X44 : $i]:
% 0.66/0.85         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.66/0.85          | (r1_tarski @ (k2_tops_1 @ X44 @ X43) @ X43)
% 0.66/0.85          | ~ (v4_pre_topc @ X43 @ X44)
% 0.66/0.85          | ~ (l1_pre_topc @ X44))),
% 0.66/0.85      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.66/0.85  thf('17', plain,
% 0.66/0.85      ((~ (l1_pre_topc @ sk_A)
% 0.66/0.85        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.66/0.85        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.66/0.85      inference('sup-', [status(thm)], ['15', '16'])).
% 0.66/0.85  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('19', plain,
% 0.66/0.85      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.66/0.85        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.66/0.85      inference('demod', [status(thm)], ['17', '18'])).
% 0.66/0.85  thf('20', plain,
% 0.66/0.85      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.66/0.85         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['14', '19'])).
% 0.66/0.85  thf(t1_xboole_1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.66/0.85       ( r1_tarski @ A @ C ) ))).
% 0.66/0.85  thf('21', plain,
% 0.66/0.85      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.66/0.85         (~ (r1_tarski @ X6 @ X7)
% 0.66/0.85          | ~ (r1_tarski @ X7 @ X8)
% 0.66/0.85          | (r1_tarski @ X6 @ X8))),
% 0.66/0.85      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.66/0.85  thf('22', plain,
% 0.66/0.85      ((![X0 : $i]:
% 0.66/0.85          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.66/0.85           | ~ (r1_tarski @ sk_B @ X0)))
% 0.66/0.85         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['20', '21'])).
% 0.66/0.85  thf('23', plain,
% 0.66/0.85      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.66/0.85         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['12', '22'])).
% 0.66/0.85  thf('24', plain,
% 0.66/0.85      (![X31 : $i, X33 : $i]:
% 0.66/0.85         ((m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X33)) | ~ (r1_tarski @ X31 @ X33))),
% 0.66/0.85      inference('cnf', [status(esa)], [t3_subset])).
% 0.66/0.85  thf('25', plain,
% 0.66/0.85      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.66/0.85         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.66/0.85         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['23', '24'])).
% 0.66/0.85  thf('26', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(redefinition_k4_subset_1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.66/0.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.66/0.85       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.66/0.85  thf('27', plain,
% 0.66/0.85      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.66/0.85         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.66/0.85          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25))
% 0.66/0.85          | ((k4_subset_1 @ X25 @ X24 @ X26) = (k2_xboole_0 @ X24 @ X26)))),
% 0.66/0.85      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.66/0.85  thf('28', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.66/0.85            = (k2_xboole_0 @ sk_B @ X0))
% 0.66/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.66/0.85      inference('sup-', [status(thm)], ['26', '27'])).
% 0.66/0.85  thf('29', plain,
% 0.66/0.85      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.66/0.85          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.66/0.85         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['25', '28'])).
% 0.66/0.85  thf('30', plain,
% 0.66/0.85      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.66/0.85         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['14', '19'])).
% 0.66/0.85  thf(t28_xboole_1, axiom,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.66/0.85  thf('31', plain,
% 0.66/0.85      (![X9 : $i, X10 : $i]:
% 0.66/0.85         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.66/0.85      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.66/0.85  thf('32', plain,
% 0.66/0.85      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.66/0.85          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.66/0.85         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['30', '31'])).
% 0.66/0.85  thf(t100_xboole_1, axiom,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.66/0.85  thf('33', plain,
% 0.66/0.85      (![X3 : $i, X4 : $i]:
% 0.66/0.85         ((k4_xboole_0 @ X3 @ X4)
% 0.66/0.85           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.66/0.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.85  thf('34', plain,
% 0.66/0.85      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.66/0.85          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.66/0.85             (k2_tops_1 @ sk_A @ sk_B))))
% 0.66/0.85         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.66/0.85      inference('sup+', [status(thm)], ['32', '33'])).
% 0.66/0.85  thf(t4_subset_1, axiom,
% 0.66/0.85    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.66/0.85  thf('35', plain,
% 0.66/0.85      (![X30 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 0.66/0.85      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.66/0.85  thf(involutiveness_k3_subset_1, axiom,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.85       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.66/0.85  thf('36', plain,
% 0.66/0.85      (![X22 : $i, X23 : $i]:
% 0.66/0.85         (((k3_subset_1 @ X23 @ (k3_subset_1 @ X23 @ X22)) = (X22))
% 0.66/0.85          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.66/0.85      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.66/0.85  thf('37', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.66/0.85      inference('sup-', [status(thm)], ['35', '36'])).
% 0.66/0.85  thf('38', plain,
% 0.66/0.85      (![X30 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 0.66/0.85      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.66/0.85  thf(d5_subset_1, axiom,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.85       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.66/0.85  thf('39', plain,
% 0.66/0.85      (![X19 : $i, X20 : $i]:
% 0.66/0.85         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.66/0.85          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.66/0.85      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.66/0.85  thf('40', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.66/0.85      inference('sup-', [status(thm)], ['38', '39'])).
% 0.66/0.85  thf(t3_boole, axiom,
% 0.66/0.85    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.66/0.85  thf('41', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.66/0.85      inference('cnf', [status(esa)], [t3_boole])).
% 0.66/0.85  thf('42', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.66/0.85      inference('sup+', [status(thm)], ['40', '41'])).
% 0.66/0.85  thf('43', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.66/0.85      inference('demod', [status(thm)], ['37', '42'])).
% 0.66/0.85  thf(dt_k2_subset_1, axiom,
% 0.66/0.85    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.66/0.85  thf('44', plain,
% 0.66/0.85      (![X21 : $i]: (m1_subset_1 @ (k2_subset_1 @ X21) @ (k1_zfmisc_1 @ X21))),
% 0.66/0.85      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.66/0.85  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.66/0.85  thf('45', plain, (![X18 : $i]: ((k2_subset_1 @ X18) = (X18))),
% 0.66/0.85      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.66/0.85  thf('46', plain, (![X21 : $i]: (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X21))),
% 0.66/0.85      inference('demod', [status(thm)], ['44', '45'])).
% 0.66/0.85  thf('47', plain,
% 0.66/0.85      (![X19 : $i, X20 : $i]:
% 0.66/0.85         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.66/0.85          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.66/0.85      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.66/0.85  thf('48', plain,
% 0.66/0.85      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.66/0.85      inference('sup-', [status(thm)], ['46', '47'])).
% 0.66/0.85  thf('49', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.66/0.85      inference('cnf', [status(esa)], [t3_boole])).
% 0.66/0.85  thf(t36_xboole_1, axiom,
% 0.66/0.85    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.66/0.85  thf('50', plain,
% 0.66/0.85      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.66/0.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.66/0.85  thf('51', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.66/0.85      inference('sup+', [status(thm)], ['49', '50'])).
% 0.66/0.85  thf('52', plain,
% 0.66/0.85      (![X9 : $i, X10 : $i]:
% 0.66/0.85         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.66/0.85      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.66/0.85  thf('53', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.66/0.85      inference('sup-', [status(thm)], ['51', '52'])).
% 0.66/0.85  thf('54', plain,
% 0.66/0.85      (![X3 : $i, X4 : $i]:
% 0.66/0.85         ((k4_xboole_0 @ X3 @ X4)
% 0.66/0.85           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.66/0.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.85  thf('55', plain,
% 0.66/0.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.66/0.85      inference('sup+', [status(thm)], ['53', '54'])).
% 0.66/0.85  thf('56', plain,
% 0.66/0.85      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.66/0.85      inference('sup+', [status(thm)], ['48', '55'])).
% 0.66/0.85  thf('57', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.66/0.85      inference('demod', [status(thm)], ['43', '56'])).
% 0.66/0.85  thf('58', plain,
% 0.66/0.85      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.66/0.85         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.66/0.85      inference('demod', [status(thm)], ['34', '57'])).
% 0.66/0.85  thf(t98_xboole_1, axiom,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.66/0.85  thf('59', plain,
% 0.66/0.85      (![X16 : $i, X17 : $i]:
% 0.66/0.85         ((k2_xboole_0 @ X16 @ X17)
% 0.66/0.85           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.66/0.85      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.66/0.85  thf('60', plain,
% 0.66/0.85      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.66/0.85          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.66/0.85         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.66/0.85      inference('sup+', [status(thm)], ['58', '59'])).
% 0.66/0.85  thf('61', plain,
% 0.66/0.85      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.66/0.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.66/0.85  thf('62', plain,
% 0.66/0.85      (![X30 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 0.66/0.85      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.66/0.85  thf('63', plain,
% 0.66/0.85      (![X31 : $i, X32 : $i]:
% 0.66/0.85         ((r1_tarski @ X31 @ X32) | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 0.66/0.85      inference('cnf', [status(esa)], [t3_subset])).
% 0.66/0.85  thf('64', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.66/0.85      inference('sup-', [status(thm)], ['62', '63'])).
% 0.66/0.85  thf(d10_xboole_0, axiom,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.66/0.85  thf('65', plain,
% 0.66/0.85      (![X0 : $i, X2 : $i]:
% 0.66/0.85         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.66/0.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.85  thf('66', plain,
% 0.66/0.85      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['64', '65'])).
% 0.66/0.85  thf('67', plain,
% 0.66/0.85      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.66/0.85      inference('sup-', [status(thm)], ['61', '66'])).
% 0.66/0.85  thf('68', plain,
% 0.66/0.85      (![X16 : $i, X17 : $i]:
% 0.66/0.85         ((k2_xboole_0 @ X16 @ X17)
% 0.66/0.85           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.66/0.85      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.66/0.85  thf('69', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.66/0.85      inference('sup+', [status(thm)], ['67', '68'])).
% 0.66/0.85  thf(t1_boole, axiom,
% 0.66/0.85    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.66/0.85  thf('70', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.66/0.85      inference('cnf', [status(esa)], [t1_boole])).
% 0.66/0.85  thf('71', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.66/0.85      inference('sup+', [status(thm)], ['69', '70'])).
% 0.66/0.85  thf('72', plain,
% 0.66/0.85      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.66/0.85         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.66/0.85      inference('demod', [status(thm)], ['60', '71'])).
% 0.66/0.85  thf('73', plain,
% 0.66/0.85      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.66/0.85          = (sk_B)))
% 0.66/0.85         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.66/0.85      inference('demod', [status(thm)], ['29', '72'])).
% 0.66/0.85  thf('74', plain,
% 0.66/0.85      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.66/0.85         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.66/0.85      inference('sup+', [status(thm)], ['9', '73'])).
% 0.66/0.85  thf('75', plain,
% 0.66/0.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.85          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.85              (k1_tops_1 @ sk_A @ sk_B)))
% 0.66/0.85        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('76', plain,
% 0.66/0.85      (~
% 0.66/0.85       (((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.85          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.85             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.66/0.85       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.66/0.85      inference('split', [status(esa)], ['75'])).
% 0.66/0.85  thf('77', plain,
% 0.66/0.85      (((k2_pre_topc @ sk_A @ sk_B)
% 0.66/0.85         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.85            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.66/0.85      inference('demod', [status(thm)], ['7', '8'])).
% 0.66/0.85  thf('78', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.66/0.85      inference('sup-', [status(thm)], ['10', '11'])).
% 0.66/0.85  thf('79', plain,
% 0.66/0.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(redefinition_k7_subset_1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.66/0.85       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.66/0.85  thf('80', plain,
% 0.66/0.85      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.66/0.85         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 0.66/0.85          | ((k7_subset_1 @ X28 @ X27 @ X29) = (k4_xboole_0 @ X27 @ X29)))),
% 0.66/0.85      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.66/0.85  thf('81', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.66/0.85           = (k4_xboole_0 @ sk_B @ X0))),
% 0.66/0.85      inference('sup-', [status(thm)], ['79', '80'])).
% 0.66/0.85  thf('82', plain,
% 0.66/0.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.85          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.85             (k1_tops_1 @ sk_A @ sk_B))))
% 0.66/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.66/0.85      inference('split', [status(esa)], ['13'])).
% 0.66/0.85  thf('83', plain,
% 0.66/0.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.85          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.66/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.66/0.85      inference('sup+', [status(thm)], ['81', '82'])).
% 0.66/0.85  thf('84', plain,
% 0.66/0.85      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.66/0.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.66/0.85  thf('85', plain,
% 0.66/0.85      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.66/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.66/0.85      inference('sup+', [status(thm)], ['83', '84'])).
% 0.66/0.85  thf('86', plain,
% 0.66/0.85      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.66/0.85         (~ (r1_tarski @ X6 @ X7)
% 0.66/0.85          | ~ (r1_tarski @ X7 @ X8)
% 0.66/0.85          | (r1_tarski @ X6 @ X8))),
% 0.66/0.85      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.66/0.85  thf('87', plain,
% 0.66/0.85      ((![X0 : $i]:
% 0.66/0.85          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.66/0.85           | ~ (r1_tarski @ sk_B @ X0)))
% 0.66/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.66/0.85      inference('sup-', [status(thm)], ['85', '86'])).
% 0.66/0.85  thf('88', plain,
% 0.66/0.85      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.66/0.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.85                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.66/0.85      inference('sup-', [status(thm)], ['78', '87'])).
% 0.66/0.85  thf('89', plain,
% 0.66/0.85      (![X31 : $i, X33 : $i]:
% 0.66/0.85         ((m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X33)) | ~ (r1_tarski @ X31 @ X33))),
% 0.66/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.66/0.86  thf('90', plain,
% 0.66/0.86      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.66/0.86         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.66/0.86         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.86                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['88', '89'])).
% 0.66/0.86  thf('91', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.66/0.86            = (k2_xboole_0 @ sk_B @ X0))
% 0.66/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['26', '27'])).
% 0.66/0.86  thf('92', plain,
% 0.66/0.86      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.66/0.86          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.66/0.86         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.86                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['90', '91'])).
% 0.66/0.86  thf('93', plain,
% 0.66/0.86      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.66/0.86         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.86                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.66/0.86      inference('sup+', [status(thm)], ['83', '84'])).
% 0.66/0.86  thf('94', plain,
% 0.66/0.86      (![X9 : $i, X10 : $i]:
% 0.66/0.86         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.66/0.86      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.66/0.86  thf('95', plain,
% 0.66/0.86      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.66/0.86          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.66/0.86         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.86                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['93', '94'])).
% 0.66/0.86  thf('96', plain,
% 0.66/0.86      (![X3 : $i, X4 : $i]:
% 0.66/0.86         ((k4_xboole_0 @ X3 @ X4)
% 0.66/0.86           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.66/0.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.86  thf('97', plain,
% 0.66/0.86      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.66/0.86          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.66/0.86             (k2_tops_1 @ sk_A @ sk_B))))
% 0.66/0.86         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.86                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.66/0.86      inference('sup+', [status(thm)], ['95', '96'])).
% 0.66/0.86  thf('98', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.66/0.86      inference('demod', [status(thm)], ['43', '56'])).
% 0.66/0.86  thf('99', plain,
% 0.66/0.86      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.66/0.86         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.86                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.66/0.86      inference('demod', [status(thm)], ['97', '98'])).
% 0.66/0.86  thf('100', plain,
% 0.66/0.86      (![X16 : $i, X17 : $i]:
% 0.66/0.86         ((k2_xboole_0 @ X16 @ X17)
% 0.66/0.86           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.66/0.86      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.66/0.86  thf('101', plain,
% 0.66/0.86      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.66/0.86          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.66/0.86         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.86                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.66/0.86      inference('sup+', [status(thm)], ['99', '100'])).
% 0.66/0.86  thf('102', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.66/0.86      inference('sup+', [status(thm)], ['69', '70'])).
% 0.66/0.86  thf('103', plain,
% 0.66/0.86      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.66/0.86         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.86                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.66/0.86      inference('demod', [status(thm)], ['101', '102'])).
% 0.66/0.86  thf('104', plain,
% 0.66/0.86      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.66/0.86          = (sk_B)))
% 0.66/0.86         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.86                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.66/0.86      inference('demod', [status(thm)], ['92', '103'])).
% 0.66/0.86  thf('105', plain,
% 0.66/0.86      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.66/0.86         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.86                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.66/0.86      inference('sup+', [status(thm)], ['77', '104'])).
% 0.66/0.86  thf('106', plain,
% 0.66/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf(fc1_tops_1, axiom,
% 0.66/0.86    (![A:$i,B:$i]:
% 0.66/0.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.66/0.86         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.66/0.86       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.66/0.86  thf('107', plain,
% 0.66/0.86      (![X37 : $i, X38 : $i]:
% 0.66/0.86         (~ (l1_pre_topc @ X37)
% 0.66/0.86          | ~ (v2_pre_topc @ X37)
% 0.66/0.86          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.66/0.86          | (v4_pre_topc @ (k2_pre_topc @ X37 @ X38) @ X37))),
% 0.66/0.86      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.66/0.86  thf('108', plain,
% 0.66/0.86      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.66/0.86        | ~ (v2_pre_topc @ sk_A)
% 0.66/0.86        | ~ (l1_pre_topc @ sk_A))),
% 0.66/0.86      inference('sup-', [status(thm)], ['106', '107'])).
% 0.66/0.86  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.66/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.86  thf('111', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.66/0.86      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.66/0.86  thf('112', plain,
% 0.66/0.86      (((v4_pre_topc @ sk_B @ sk_A))
% 0.66/0.86         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.86                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.66/0.86      inference('sup+', [status(thm)], ['105', '111'])).
% 0.66/0.86  thf('113', plain,
% 0.66/0.86      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.66/0.86      inference('split', [status(esa)], ['75'])).
% 0.66/0.86  thf('114', plain,
% 0.66/0.86      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.66/0.86       ~
% 0.66/0.86       (((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.86             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.66/0.86      inference('sup-', [status(thm)], ['112', '113'])).
% 0.66/0.86  thf('115', plain,
% 0.66/0.86      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.66/0.86       (((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.86             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.66/0.86      inference('split', [status(esa)], ['13'])).
% 0.66/0.86  thf('116', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.66/0.86      inference('sat_resolution*', [status(thm)], ['76', '114', '115'])).
% 0.66/0.86  thf('117', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.66/0.86      inference('simpl_trail', [status(thm)], ['74', '116'])).
% 0.66/0.86  thf('118', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.66/0.86           = (k4_xboole_0 @ sk_B @ X0))),
% 0.66/0.86      inference('sup-', [status(thm)], ['79', '80'])).
% 0.66/0.86  thf('119', plain,
% 0.66/0.86      (((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.66/0.86      inference('demod', [status(thm)], ['4', '117', '118'])).
% 0.66/0.86  thf('120', plain,
% 0.66/0.86      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.86              (k1_tops_1 @ sk_A @ sk_B))))
% 0.66/0.86         <= (~
% 0.66/0.86             (((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.86                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.66/0.86      inference('split', [status(esa)], ['75'])).
% 0.66/0.86  thf('121', plain,
% 0.66/0.86      (![X0 : $i]:
% 0.66/0.86         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.66/0.86           = (k4_xboole_0 @ sk_B @ X0))),
% 0.66/0.86      inference('sup-', [status(thm)], ['79', '80'])).
% 0.66/0.86  thf('122', plain,
% 0.66/0.86      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.66/0.86         <= (~
% 0.66/0.86             (((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.86                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.66/0.86      inference('demod', [status(thm)], ['120', '121'])).
% 0.66/0.86  thf('123', plain,
% 0.66/0.86      (~
% 0.66/0.86       (((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.66/0.86             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.66/0.86      inference('sat_resolution*', [status(thm)], ['76', '114'])).
% 0.66/0.86  thf('124', plain,
% 0.66/0.86      (((k2_tops_1 @ sk_A @ sk_B)
% 0.66/0.86         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.66/0.86      inference('simpl_trail', [status(thm)], ['122', '123'])).
% 0.66/0.86  thf('125', plain, ($false),
% 0.66/0.86      inference('simplify_reflect-', [status(thm)], ['119', '124'])).
% 0.66/0.86  
% 0.66/0.86  % SZS output end Refutation
% 0.66/0.86  
% 0.66/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
