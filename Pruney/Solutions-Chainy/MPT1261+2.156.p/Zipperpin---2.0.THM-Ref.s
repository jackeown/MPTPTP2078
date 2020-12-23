%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.161UFxYbns

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:01 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 665 expanded)
%              Number of leaves         :   39 ( 219 expanded)
%              Depth                    :   18
%              Number of atoms          : 1587 (6923 expanded)
%              Number of equality atoms :  115 ( 447 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X24 @ ( k3_subset_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','5'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('14',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( ( k2_tops_1 @ X43 @ X42 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X43 ) @ ( k2_pre_topc @ X43 @ X42 ) @ ( k1_tops_1 @ X43 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['6','11'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( ( k2_pre_topc @ X45 @ X44 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X45 ) @ X44 @ ( k2_tops_1 @ X45 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('29',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X47 @ X46 ) @ X46 )
      | ~ ( v4_pre_topc @ X46 @ X47 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','35'])).

thf('37',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('40',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k4_subset_1 @ X26 @ X25 @ X27 )
        = ( k2_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('45',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('47',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('50',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('51',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X24 @ ( k3_subset_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('54',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('60',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('63',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('66',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('67',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('69',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('74',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['61','64','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('79',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('86',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['49','84','85'])).

thf('87',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['42','86'])).

thf('88',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['22','87'])).

thf('89',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['89'])).

thf('91',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('92',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('93',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k4_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['26'])).

thf('96',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('98',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('99',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['96','101'])).

thf('103',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('104',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('106',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('108',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('109',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('111',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('113',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','83'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('116',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['106','116'])).

thf('118',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['91','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('120',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X40 @ X41 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('121',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['118','124'])).

thf('126',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['89'])).

thf('127',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['26'])).

thf('129',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['90','127','128'])).

thf('130',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['88','129'])).

thf('131',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['6','11'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','130','131','132','133'])).

thf('135',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['89'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('137',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['90','127'])).

thf('139',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['137','138'])).

thf('140',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['134','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.161UFxYbns
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:08:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.73  % Solved by: fo/fo7.sh
% 0.53/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.73  % done 923 iterations in 0.261s
% 0.53/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.73  % SZS output start Refutation
% 0.53/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.73  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.53/0.73  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.53/0.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.53/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.73  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.53/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.73  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.53/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.73  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.53/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.73  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.53/0.73  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.53/0.73  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.53/0.73  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.53/0.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.53/0.73  thf(t77_tops_1, conjecture,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.73       ( ![B:$i]:
% 0.53/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.73           ( ( v4_pre_topc @ B @ A ) <=>
% 0.53/0.73             ( ( k2_tops_1 @ A @ B ) =
% 0.53/0.73               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.53/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.73    (~( ![A:$i]:
% 0.53/0.73        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.73          ( ![B:$i]:
% 0.53/0.73            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.73              ( ( v4_pre_topc @ B @ A ) <=>
% 0.53/0.73                ( ( k2_tops_1 @ A @ B ) =
% 0.53/0.73                  ( k7_subset_1 @
% 0.53/0.73                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.53/0.73    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.53/0.73  thf('0', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(involutiveness_k3_subset_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.73       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.53/0.73  thf('1', plain,
% 0.53/0.73      (![X23 : $i, X24 : $i]:
% 0.53/0.73         (((k3_subset_1 @ X24 @ (k3_subset_1 @ X24 @ X23)) = (X23))
% 0.53/0.73          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.53/0.73      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.53/0.73  thf('2', plain,
% 0.53/0.73      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.73         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.53/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.53/0.73  thf('3', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(d5_subset_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.73       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.53/0.73  thf('4', plain,
% 0.53/0.73      (![X18 : $i, X19 : $i]:
% 0.53/0.73         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 0.53/0.73          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.53/0.73      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.53/0.73  thf('5', plain,
% 0.53/0.73      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.53/0.73         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.53/0.73      inference('sup-', [status(thm)], ['3', '4'])).
% 0.53/0.73  thf('6', plain,
% 0.53/0.73      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.73         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.53/0.73      inference('demod', [status(thm)], ['2', '5'])).
% 0.53/0.73  thf(t36_xboole_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.53/0.73  thf('7', plain,
% 0.53/0.73      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.53/0.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.53/0.73  thf(t3_subset, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.53/0.73  thf('8', plain,
% 0.53/0.73      (![X34 : $i, X36 : $i]:
% 0.53/0.73         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 0.53/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.73  thf('9', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.53/0.73      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.73  thf('10', plain,
% 0.53/0.73      (![X18 : $i, X19 : $i]:
% 0.53/0.73         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 0.53/0.73          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.53/0.73      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.53/0.73  thf('11', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.53/0.73           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.53/0.73  thf('12', plain,
% 0.53/0.73      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.73         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.53/0.73      inference('demod', [status(thm)], ['6', '11'])).
% 0.53/0.73  thf('13', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.53/0.73      inference('sup-', [status(thm)], ['7', '8'])).
% 0.53/0.73  thf(l78_tops_1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( l1_pre_topc @ A ) =>
% 0.53/0.73       ( ![B:$i]:
% 0.53/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.73           ( ( k2_tops_1 @ A @ B ) =
% 0.53/0.73             ( k7_subset_1 @
% 0.53/0.73               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.53/0.73               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.53/0.73  thf('14', plain,
% 0.53/0.73      (![X42 : $i, X43 : $i]:
% 0.53/0.73         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.53/0.73          | ((k2_tops_1 @ X43 @ X42)
% 0.53/0.73              = (k7_subset_1 @ (u1_struct_0 @ X43) @ 
% 0.53/0.73                 (k2_pre_topc @ X43 @ X42) @ (k1_tops_1 @ X43 @ X42)))
% 0.53/0.73          | ~ (l1_pre_topc @ X43))),
% 0.53/0.73      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.53/0.73  thf('15', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (~ (l1_pre_topc @ X0)
% 0.53/0.73          | ((k2_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.53/0.73              = (k7_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.53/0.73                 (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.53/0.73                 (k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['13', '14'])).
% 0.53/0.73  thf('16', plain,
% 0.53/0.73      ((((k2_tops_1 @ sk_A @ 
% 0.53/0.73          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.73           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.53/0.73          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.73             (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.53/0.73             (k1_tops_1 @ sk_A @ 
% 0.53/0.73              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.73               (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))))
% 0.53/0.73        | ~ (l1_pre_topc @ sk_A))),
% 0.53/0.73      inference('sup+', [status(thm)], ['12', '15'])).
% 0.53/0.73  thf('17', plain,
% 0.53/0.73      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.73         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.53/0.73      inference('demod', [status(thm)], ['6', '11'])).
% 0.53/0.73  thf('18', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(t65_tops_1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( l1_pre_topc @ A ) =>
% 0.53/0.73       ( ![B:$i]:
% 0.53/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.73           ( ( k2_pre_topc @ A @ B ) =
% 0.53/0.73             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.53/0.73  thf('19', plain,
% 0.53/0.73      (![X44 : $i, X45 : $i]:
% 0.53/0.73         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.53/0.73          | ((k2_pre_topc @ X45 @ X44)
% 0.53/0.73              = (k4_subset_1 @ (u1_struct_0 @ X45) @ X44 @ 
% 0.53/0.73                 (k2_tops_1 @ X45 @ X44)))
% 0.53/0.73          | ~ (l1_pre_topc @ X45))),
% 0.53/0.73      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.53/0.73  thf('20', plain,
% 0.53/0.73      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.73        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.53/0.73            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['18', '19'])).
% 0.53/0.73  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('22', plain,
% 0.53/0.73      (((k2_pre_topc @ sk_A @ sk_B)
% 0.53/0.73         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.73      inference('demod', [status(thm)], ['20', '21'])).
% 0.53/0.73  thf('23', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('24', plain,
% 0.53/0.73      (![X34 : $i, X35 : $i]:
% 0.53/0.73         ((r1_tarski @ X34 @ X35) | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.73  thf('25', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.53/0.73      inference('sup-', [status(thm)], ['23', '24'])).
% 0.53/0.73  thf('26', plain,
% 0.53/0.73      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73             (k1_tops_1 @ sk_A @ sk_B)))
% 0.53/0.73        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('27', plain,
% 0.53/0.73      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.73      inference('split', [status(esa)], ['26'])).
% 0.53/0.73  thf('28', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(t69_tops_1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( l1_pre_topc @ A ) =>
% 0.53/0.73       ( ![B:$i]:
% 0.53/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.73           ( ( v4_pre_topc @ B @ A ) =>
% 0.53/0.73             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.53/0.73  thf('29', plain,
% 0.53/0.73      (![X46 : $i, X47 : $i]:
% 0.53/0.73         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 0.53/0.73          | (r1_tarski @ (k2_tops_1 @ X47 @ X46) @ X46)
% 0.53/0.73          | ~ (v4_pre_topc @ X46 @ X47)
% 0.53/0.73          | ~ (l1_pre_topc @ X47))),
% 0.53/0.73      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.53/0.73  thf('30', plain,
% 0.53/0.73      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.73        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.53/0.73        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.53/0.73      inference('sup-', [status(thm)], ['28', '29'])).
% 0.53/0.73  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('32', plain,
% 0.53/0.73      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.53/0.73        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.53/0.73      inference('demod', [status(thm)], ['30', '31'])).
% 0.53/0.73  thf('33', plain,
% 0.53/0.73      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.53/0.73         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['27', '32'])).
% 0.53/0.73  thf(t1_xboole_1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.53/0.73       ( r1_tarski @ A @ C ) ))).
% 0.53/0.73  thf('34', plain,
% 0.53/0.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.53/0.73         (~ (r1_tarski @ X8 @ X9)
% 0.53/0.73          | ~ (r1_tarski @ X9 @ X10)
% 0.53/0.73          | (r1_tarski @ X8 @ X10))),
% 0.53/0.73      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.53/0.73  thf('35', plain,
% 0.53/0.73      ((![X0 : $i]:
% 0.53/0.73          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.53/0.73           | ~ (r1_tarski @ sk_B @ X0)))
% 0.53/0.73         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['33', '34'])).
% 0.53/0.73  thf('36', plain,
% 0.53/0.73      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.53/0.73         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['25', '35'])).
% 0.53/0.73  thf('37', plain,
% 0.53/0.73      (![X34 : $i, X36 : $i]:
% 0.53/0.73         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 0.53/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.73  thf('38', plain,
% 0.53/0.73      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.53/0.73         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.53/0.73         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['36', '37'])).
% 0.53/0.73  thf('39', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(redefinition_k4_subset_1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.53/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.53/0.73       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.53/0.73  thf('40', plain,
% 0.53/0.73      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.53/0.73         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.53/0.73          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26))
% 0.53/0.73          | ((k4_subset_1 @ X26 @ X25 @ X27) = (k2_xboole_0 @ X25 @ X27)))),
% 0.53/0.73      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.53/0.73  thf('41', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.53/0.73            = (k2_xboole_0 @ sk_B @ X0))
% 0.53/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['39', '40'])).
% 0.53/0.73  thf('42', plain,
% 0.53/0.73      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.53/0.73          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.53/0.73         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['38', '41'])).
% 0.53/0.73  thf('43', plain,
% 0.53/0.73      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.53/0.73         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['27', '32'])).
% 0.53/0.73  thf(t28_xboole_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.53/0.73  thf('44', plain,
% 0.53/0.73      (![X11 : $i, X12 : $i]:
% 0.53/0.73         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.53/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.73  thf('45', plain,
% 0.53/0.73      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.53/0.73          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.53/0.73         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['43', '44'])).
% 0.53/0.73  thf(t100_xboole_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.53/0.73  thf('46', plain,
% 0.53/0.73      (![X3 : $i, X4 : $i]:
% 0.53/0.73         ((k4_xboole_0 @ X3 @ X4)
% 0.53/0.73           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.73  thf(t98_xboole_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.53/0.73  thf('47', plain,
% 0.53/0.73      (![X15 : $i, X16 : $i]:
% 0.53/0.73         ((k2_xboole_0 @ X15 @ X16)
% 0.53/0.73           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.53/0.73  thf('48', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k2_xboole_0 @ X0 @ X1)
% 0.53/0.73           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['46', '47'])).
% 0.53/0.73  thf('49', plain,
% 0.53/0.73      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.53/0.73          = (k5_xboole_0 @ sk_B @ 
% 0.53/0.73             (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.53/0.73              (k2_tops_1 @ sk_A @ sk_B)))))
% 0.53/0.73         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['45', '48'])).
% 0.53/0.73  thf(t4_subset_1, axiom,
% 0.53/0.73    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.53/0.73  thf('50', plain,
% 0.53/0.73      (![X33 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X33))),
% 0.53/0.73      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.53/0.73  thf('51', plain,
% 0.53/0.73      (![X23 : $i, X24 : $i]:
% 0.53/0.73         (((k3_subset_1 @ X24 @ (k3_subset_1 @ X24 @ X23)) = (X23))
% 0.53/0.73          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.53/0.73      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.53/0.73  thf('52', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.53/0.73      inference('sup-', [status(thm)], ['50', '51'])).
% 0.53/0.73  thf('53', plain,
% 0.53/0.73      (![X33 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X33))),
% 0.53/0.73      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.53/0.73  thf('54', plain,
% 0.53/0.73      (![X18 : $i, X19 : $i]:
% 0.53/0.73         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 0.53/0.73          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.53/0.73      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.53/0.73  thf('55', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.53/0.73      inference('sup-', [status(thm)], ['53', '54'])).
% 0.53/0.73  thf('56', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.53/0.73      inference('demod', [status(thm)], ['52', '55'])).
% 0.53/0.73  thf('57', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.53/0.73           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.53/0.73  thf('58', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.53/0.73      inference('demod', [status(thm)], ['56', '57'])).
% 0.53/0.73  thf('59', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.53/0.73      inference('demod', [status(thm)], ['56', '57'])).
% 0.53/0.73  thf('60', plain,
% 0.53/0.73      (![X15 : $i, X16 : $i]:
% 0.53/0.73         ((k2_xboole_0 @ X15 @ X16)
% 0.53/0.73           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.53/0.73  thf('61', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ X0)
% 0.53/0.73           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['59', '60'])).
% 0.53/0.73  thf('62', plain,
% 0.53/0.73      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.53/0.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.53/0.73  thf(t12_xboole_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.53/0.73  thf('63', plain,
% 0.53/0.73      (![X5 : $i, X6 : $i]:
% 0.53/0.73         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.53/0.73      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.53/0.73  thf('64', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.53/0.73      inference('sup-', [status(thm)], ['62', '63'])).
% 0.53/0.73  thf('65', plain,
% 0.53/0.73      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.53/0.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.53/0.73  thf('66', plain,
% 0.53/0.73      (![X33 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X33))),
% 0.53/0.73      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.53/0.73  thf('67', plain,
% 0.53/0.73      (![X34 : $i, X35 : $i]:
% 0.53/0.73         ((r1_tarski @ X34 @ X35) | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.73  thf('68', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.53/0.73      inference('sup-', [status(thm)], ['66', '67'])).
% 0.53/0.73  thf(d10_xboole_0, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.73  thf('69', plain,
% 0.53/0.73      (![X0 : $i, X2 : $i]:
% 0.53/0.73         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.53/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.73  thf('70', plain,
% 0.53/0.73      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['68', '69'])).
% 0.53/0.73  thf('71', plain,
% 0.53/0.73      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.53/0.73      inference('sup-', [status(thm)], ['65', '70'])).
% 0.53/0.73  thf('72', plain,
% 0.53/0.73      (![X15 : $i, X16 : $i]:
% 0.53/0.73         ((k2_xboole_0 @ X15 @ X16)
% 0.53/0.73           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.53/0.73  thf('73', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['71', '72'])).
% 0.53/0.73  thf(t1_boole, axiom,
% 0.53/0.73    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.53/0.73  thf('74', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.53/0.73      inference('cnf', [status(esa)], [t1_boole])).
% 0.53/0.73  thf('75', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['73', '74'])).
% 0.53/0.73  thf('76', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.53/0.73      inference('demod', [status(thm)], ['61', '64', '75'])).
% 0.53/0.73  thf('77', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.73      inference('demod', [status(thm)], ['58', '76'])).
% 0.53/0.73  thf('78', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.53/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.73  thf('79', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.53/0.73      inference('simplify', [status(thm)], ['78'])).
% 0.53/0.73  thf('80', plain,
% 0.53/0.73      (![X11 : $i, X12 : $i]:
% 0.53/0.73         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.53/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.73  thf('81', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.53/0.73      inference('sup-', [status(thm)], ['79', '80'])).
% 0.53/0.73  thf('82', plain,
% 0.53/0.73      (![X3 : $i, X4 : $i]:
% 0.53/0.73         ((k4_xboole_0 @ X3 @ X4)
% 0.53/0.73           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.73  thf('83', plain,
% 0.53/0.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['81', '82'])).
% 0.53/0.73  thf('84', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.73      inference('demod', [status(thm)], ['77', '83'])).
% 0.53/0.73  thf('85', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['73', '74'])).
% 0.53/0.73  thf('86', plain,
% 0.53/0.73      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.53/0.73         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.73      inference('demod', [status(thm)], ['49', '84', '85'])).
% 0.53/0.73  thf('87', plain,
% 0.53/0.73      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.53/0.73          = (sk_B)))
% 0.53/0.73         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.73      inference('demod', [status(thm)], ['42', '86'])).
% 0.53/0.73  thf('88', plain,
% 0.53/0.73      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.53/0.73         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.73      inference('sup+', [status(thm)], ['22', '87'])).
% 0.53/0.73  thf('89', plain,
% 0.53/0.73      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73              (k1_tops_1 @ sk_A @ sk_B)))
% 0.53/0.73        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('90', plain,
% 0.53/0.73      (~
% 0.53/0.73       (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.53/0.73       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.53/0.73      inference('split', [status(esa)], ['89'])).
% 0.53/0.73  thf('91', plain,
% 0.53/0.73      (((k2_pre_topc @ sk_A @ sk_B)
% 0.53/0.73         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.73      inference('demod', [status(thm)], ['20', '21'])).
% 0.53/0.73  thf('92', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(redefinition_k7_subset_1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.73       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.53/0.73  thf('93', plain,
% 0.53/0.73      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.53/0.73         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.53/0.73          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k4_xboole_0 @ X28 @ X30)))),
% 0.53/0.73      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.53/0.73  thf('94', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.53/0.73           = (k4_xboole_0 @ sk_B @ X0))),
% 0.53/0.73      inference('sup-', [status(thm)], ['92', '93'])).
% 0.53/0.73  thf('95', plain,
% 0.53/0.73      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73             (k1_tops_1 @ sk_A @ sk_B))))
% 0.53/0.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('split', [status(esa)], ['26'])).
% 0.53/0.73  thf('96', plain,
% 0.53/0.73      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.53/0.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['94', '95'])).
% 0.53/0.73  thf('97', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.53/0.73      inference('sup-', [status(thm)], ['23', '24'])).
% 0.53/0.73  thf('98', plain,
% 0.53/0.73      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.53/0.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.53/0.73  thf('99', plain,
% 0.53/0.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.53/0.73         (~ (r1_tarski @ X8 @ X9)
% 0.53/0.73          | ~ (r1_tarski @ X9 @ X10)
% 0.53/0.73          | (r1_tarski @ X8 @ X10))),
% 0.53/0.73      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.53/0.73  thf('100', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.53/0.73      inference('sup-', [status(thm)], ['98', '99'])).
% 0.53/0.73  thf('101', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.53/0.73      inference('sup-', [status(thm)], ['97', '100'])).
% 0.53/0.73  thf('102', plain,
% 0.53/0.73      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.53/0.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['96', '101'])).
% 0.53/0.73  thf('103', plain,
% 0.53/0.73      (![X34 : $i, X36 : $i]:
% 0.53/0.73         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 0.53/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.73  thf('104', plain,
% 0.53/0.73      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.53/0.73         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.53/0.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['102', '103'])).
% 0.53/0.73  thf('105', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.53/0.73            = (k2_xboole_0 @ sk_B @ X0))
% 0.53/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['39', '40'])).
% 0.53/0.73  thf('106', plain,
% 0.53/0.73      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.53/0.73          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.53/0.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['104', '105'])).
% 0.53/0.73  thf('107', plain,
% 0.53/0.73      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.53/0.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['94', '95'])).
% 0.53/0.73  thf('108', plain,
% 0.53/0.73      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.53/0.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.53/0.73  thf('109', plain,
% 0.53/0.73      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.53/0.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['107', '108'])).
% 0.53/0.73  thf('110', plain,
% 0.53/0.73      (![X11 : $i, X12 : $i]:
% 0.53/0.73         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.53/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.73  thf('111', plain,
% 0.53/0.73      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.53/0.73          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.53/0.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['109', '110'])).
% 0.53/0.73  thf('112', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         ((k2_xboole_0 @ X0 @ X1)
% 0.53/0.73           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['46', '47'])).
% 0.53/0.73  thf('113', plain,
% 0.53/0.73      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.53/0.73          = (k5_xboole_0 @ sk_B @ 
% 0.53/0.73             (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.53/0.73              (k2_tops_1 @ sk_A @ sk_B)))))
% 0.53/0.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['111', '112'])).
% 0.53/0.73  thf('114', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.73      inference('demod', [status(thm)], ['77', '83'])).
% 0.53/0.73  thf('115', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.53/0.73      inference('sup+', [status(thm)], ['73', '74'])).
% 0.53/0.73  thf('116', plain,
% 0.53/0.73      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.53/0.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.53/0.73  thf('117', plain,
% 0.53/0.73      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.53/0.73          = (sk_B)))
% 0.53/0.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('demod', [status(thm)], ['106', '116'])).
% 0.53/0.73  thf('118', plain,
% 0.53/0.73      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.53/0.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['91', '117'])).
% 0.53/0.73  thf('119', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(fc1_tops_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.53/0.73         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.53/0.73       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.53/0.73  thf('120', plain,
% 0.53/0.73      (![X40 : $i, X41 : $i]:
% 0.53/0.73         (~ (l1_pre_topc @ X40)
% 0.53/0.73          | ~ (v2_pre_topc @ X40)
% 0.53/0.73          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.53/0.73          | (v4_pre_topc @ (k2_pre_topc @ X40 @ X41) @ X40))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.53/0.73  thf('121', plain,
% 0.53/0.73      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.53/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.53/0.73        | ~ (l1_pre_topc @ sk_A))),
% 0.53/0.73      inference('sup-', [status(thm)], ['119', '120'])).
% 0.53/0.73  thf('122', plain, ((v2_pre_topc @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('123', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('124', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.53/0.73      inference('demod', [status(thm)], ['121', '122', '123'])).
% 0.53/0.73  thf('125', plain,
% 0.53/0.73      (((v4_pre_topc @ sk_B @ sk_A))
% 0.53/0.73         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('sup+', [status(thm)], ['118', '124'])).
% 0.53/0.73  thf('126', plain,
% 0.53/0.73      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.73      inference('split', [status(esa)], ['89'])).
% 0.53/0.73  thf('127', plain,
% 0.53/0.73      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.53/0.73       ~
% 0.53/0.73       (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['125', '126'])).
% 0.53/0.73  thf('128', plain,
% 0.53/0.73      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.53/0.73       (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.53/0.73      inference('split', [status(esa)], ['26'])).
% 0.53/0.73  thf('129', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.53/0.73      inference('sat_resolution*', [status(thm)], ['90', '127', '128'])).
% 0.53/0.73  thf('130', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.53/0.73      inference('simpl_trail', [status(thm)], ['88', '129'])).
% 0.53/0.73  thf('131', plain,
% 0.53/0.73      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.73         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.53/0.73      inference('demod', [status(thm)], ['6', '11'])).
% 0.53/0.73  thf('132', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.53/0.73           = (k4_xboole_0 @ sk_B @ X0))),
% 0.53/0.73      inference('sup-', [status(thm)], ['92', '93'])).
% 0.53/0.73  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('134', plain,
% 0.53/0.73      (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.73      inference('demod', [status(thm)],
% 0.53/0.73                ['16', '17', '130', '131', '132', '133'])).
% 0.53/0.73  thf('135', plain,
% 0.53/0.73      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73              (k1_tops_1 @ sk_A @ sk_B))))
% 0.53/0.73         <= (~
% 0.53/0.73             (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('split', [status(esa)], ['89'])).
% 0.53/0.73  thf('136', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.53/0.73           = (k4_xboole_0 @ sk_B @ X0))),
% 0.53/0.73      inference('sup-', [status(thm)], ['92', '93'])).
% 0.53/0.73  thf('137', plain,
% 0.53/0.73      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.53/0.73         <= (~
% 0.53/0.73             (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.53/0.73      inference('demod', [status(thm)], ['135', '136'])).
% 0.53/0.73  thf('138', plain,
% 0.53/0.73      (~
% 0.53/0.73       (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.53/0.73             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.53/0.73      inference('sat_resolution*', [status(thm)], ['90', '127'])).
% 0.53/0.73  thf('139', plain,
% 0.53/0.73      (((k2_tops_1 @ sk_A @ sk_B)
% 0.53/0.73         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.53/0.73      inference('simpl_trail', [status(thm)], ['137', '138'])).
% 0.53/0.73  thf('140', plain, ($false),
% 0.53/0.73      inference('simplify_reflect-', [status(thm)], ['134', '139'])).
% 0.53/0.73  
% 0.53/0.73  % SZS output end Refutation
% 0.53/0.73  
% 0.53/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
