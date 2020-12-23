%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IBo2FMVuKk

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:53 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 407 expanded)
%              Number of leaves         :   31 ( 124 expanded)
%              Depth                    :   18
%              Number of atoms          : 1093 (5625 expanded)
%              Number of equality atoms :   74 ( 318 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k1_tops_1 @ X34 @ X33 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 @ ( k2_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X21 @ X23 )
        = ( k4_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','6'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X24: $i,X26: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','6'])).

thf('15',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('19',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X32 @ X31 ) @ X31 )
      | ~ ( v4_pre_topc @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X24: $i,X26: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k2_pre_topc @ X30 @ X29 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 @ ( k2_tops_1 @ X30 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('34',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k4_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X24: $i,X26: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('45',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k4_subset_1 @ X19 @ X18 @ X20 )
        = ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','54'])).

thf('56',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['32','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('58',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v2_pre_topc @ X28 )
      | ( ( k2_pre_topc @ X28 @ X27 )
       != X27 )
      | ( v4_pre_topc @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['26'])).

thf('66',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('68',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['27','66','67'])).

thf('69',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['25','68'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('70',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('71',plain,
    ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('73',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('74',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','6'])).

thf('76',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['27','66','67'])).

thf('78',plain,
    ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['71','78'])).

thf('80',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['15','79'])).

thf('81',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['26'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('83',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['27','66'])).

thf('85',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['83','84'])).

thf('86',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['80','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IBo2FMVuKk
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 477 iterations in 0.154s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.40/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.60  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.40/0.60  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.40/0.60  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.40/0.60  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.40/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.60  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.40/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.60  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.40/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.60  thf(t77_tops_1, conjecture,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.60           ( ( v4_pre_topc @ B @ A ) <=>
% 0.40/0.60             ( ( k2_tops_1 @ A @ B ) =
% 0.40/0.60               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i]:
% 0.40/0.60        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.60          ( ![B:$i]:
% 0.40/0.60            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.60              ( ( v4_pre_topc @ B @ A ) <=>
% 0.40/0.60                ( ( k2_tops_1 @ A @ B ) =
% 0.40/0.60                  ( k7_subset_1 @
% 0.40/0.60                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.40/0.60  thf('0', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(t74_tops_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( l1_pre_topc @ A ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.60           ( ( k1_tops_1 @ A @ B ) =
% 0.40/0.60             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.40/0.60  thf('1', plain,
% 0.40/0.60      (![X33 : $i, X34 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.40/0.60          | ((k1_tops_1 @ X34 @ X33)
% 0.40/0.60              = (k7_subset_1 @ (u1_struct_0 @ X34) @ X33 @ 
% 0.40/0.60                 (k2_tops_1 @ X34 @ X33)))
% 0.40/0.60          | ~ (l1_pre_topc @ X34))),
% 0.40/0.60      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.40/0.60  thf('2', plain,
% 0.40/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.60        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.40/0.60            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.60  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('4', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(redefinition_k7_subset_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.60       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.40/0.60  thf('5', plain,
% 0.40/0.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.40/0.60          | ((k7_subset_1 @ X22 @ X21 @ X23) = (k4_xboole_0 @ X21 @ X23)))),
% 0.40/0.60      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.40/0.60  thf('6', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.40/0.60           = (k4_xboole_0 @ sk_B @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.60  thf('7', plain,
% 0.40/0.60      (((k1_tops_1 @ sk_A @ sk_B)
% 0.40/0.60         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.60      inference('demod', [status(thm)], ['2', '3', '6'])).
% 0.40/0.60  thf(t36_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.40/0.60  thf('8', plain,
% 0.40/0.60      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.40/0.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.40/0.60  thf(t3_subset, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.60  thf('9', plain,
% 0.40/0.60      (![X24 : $i, X26 : $i]:
% 0.40/0.60         ((m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X24 @ X26))),
% 0.40/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.60  thf('10', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.40/0.60  thf(d5_subset_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.60       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.40/0.60  thf('11', plain,
% 0.40/0.60      (![X12 : $i, X13 : $i]:
% 0.40/0.60         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 0.40/0.60          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.40/0.60  thf('12', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.40/0.60           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.40/0.60  thf('13', plain,
% 0.40/0.60      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.40/0.60         = (k4_xboole_0 @ sk_B @ 
% 0.40/0.60            (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['7', '12'])).
% 0.40/0.60  thf('14', plain,
% 0.40/0.60      (((k1_tops_1 @ sk_A @ sk_B)
% 0.40/0.60         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.60      inference('demod', [status(thm)], ['2', '3', '6'])).
% 0.40/0.60  thf('15', plain,
% 0.40/0.60      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.40/0.60         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.60      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60             (k1_tops_1 @ sk_A @ sk_B)))
% 0.40/0.60        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('17', plain,
% 0.40/0.60      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.60      inference('split', [status(esa)], ['16'])).
% 0.40/0.60  thf('18', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(t69_tops_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( l1_pre_topc @ A ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.60           ( ( v4_pre_topc @ B @ A ) =>
% 0.40/0.60             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.40/0.60  thf('19', plain,
% 0.40/0.60      (![X31 : $i, X32 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.40/0.60          | (r1_tarski @ (k2_tops_1 @ X32 @ X31) @ X31)
% 0.40/0.60          | ~ (v4_pre_topc @ X31 @ X32)
% 0.40/0.60          | ~ (l1_pre_topc @ X32))),
% 0.40/0.60      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.40/0.60  thf('20', plain,
% 0.40/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.60        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.40/0.60        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.40/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.60  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('22', plain,
% 0.40/0.60      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.40/0.60        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.40/0.60      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.60  thf('23', plain,
% 0.40/0.60      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.40/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['17', '22'])).
% 0.40/0.60  thf('24', plain,
% 0.40/0.60      (![X24 : $i, X26 : $i]:
% 0.40/0.60         ((m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X24 @ X26))),
% 0.40/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.60  thf('25', plain,
% 0.40/0.60      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.40/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.40/0.60  thf('26', plain,
% 0.40/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60              (k1_tops_1 @ sk_A @ sk_B)))
% 0.40/0.60        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('27', plain,
% 0.40/0.60      (~
% 0.40/0.60       (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.40/0.60       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.40/0.60      inference('split', [status(esa)], ['26'])).
% 0.40/0.60  thf('28', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(t65_tops_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( l1_pre_topc @ A ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.60           ( ( k2_pre_topc @ A @ B ) =
% 0.40/0.60             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.40/0.60  thf('29', plain,
% 0.40/0.60      (![X29 : $i, X30 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.40/0.60          | ((k2_pre_topc @ X30 @ X29)
% 0.40/0.60              = (k4_subset_1 @ (u1_struct_0 @ X30) @ X29 @ 
% 0.40/0.60                 (k2_tops_1 @ X30 @ X29)))
% 0.40/0.60          | ~ (l1_pre_topc @ X30))),
% 0.40/0.60      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.40/0.60  thf('30', plain,
% 0.40/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.60        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.40/0.60            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.40/0.60  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('32', plain,
% 0.40/0.60      (((k2_pre_topc @ sk_A @ sk_B)
% 0.40/0.60         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.60      inference('demod', [status(thm)], ['30', '31'])).
% 0.40/0.60  thf('33', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.40/0.60           = (k4_xboole_0 @ sk_B @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.60  thf('34', plain,
% 0.40/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60             (k1_tops_1 @ sk_A @ sk_B))))
% 0.40/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('split', [status(esa)], ['16'])).
% 0.40/0.60  thf('35', plain,
% 0.40/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.40/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['33', '34'])).
% 0.40/0.60  thf('36', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('37', plain,
% 0.40/0.60      (![X24 : $i, X25 : $i]:
% 0.40/0.60         ((r1_tarski @ X24 @ X25) | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.60  thf('38', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.40/0.60  thf(t109_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.40/0.60  thf('39', plain,
% 0.40/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.40/0.60         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ (k4_xboole_0 @ X5 @ X7) @ X6))),
% 0.40/0.60      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.40/0.60  thf('40', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['38', '39'])).
% 0.40/0.60  thf('41', plain,
% 0.40/0.60      (![X24 : $i, X26 : $i]:
% 0.40/0.60         ((m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X24 @ X26))),
% 0.40/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.60  thf('42', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.40/0.60          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.40/0.60  thf('43', plain,
% 0.40/0.60      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.40/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.40/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['35', '42'])).
% 0.40/0.60  thf('44', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(redefinition_k4_subset_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.40/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.40/0.60       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.40/0.60  thf('45', plain,
% 0.40/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.40/0.60          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19))
% 0.40/0.60          | ((k4_subset_1 @ X19 @ X18 @ X20) = (k2_xboole_0 @ X18 @ X20)))),
% 0.40/0.60      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.40/0.60  thf('46', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.40/0.60            = (k2_xboole_0 @ sk_B @ X0))
% 0.40/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.40/0.60  thf('47', plain,
% 0.40/0.60      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.40/0.60          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.40/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['43', '46'])).
% 0.40/0.60  thf('48', plain,
% 0.40/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.40/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['33', '34'])).
% 0.40/0.60  thf('49', plain,
% 0.40/0.60      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.40/0.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.40/0.60  thf(t12_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.40/0.60  thf('50', plain,
% 0.40/0.60      (![X8 : $i, X9 : $i]:
% 0.40/0.60         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.40/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.40/0.60  thf('51', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['49', '50'])).
% 0.40/0.60  thf(commutativity_k2_xboole_0, axiom,
% 0.40/0.60    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.40/0.60  thf('52', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.40/0.60  thf('53', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.40/0.60      inference('demod', [status(thm)], ['51', '52'])).
% 0.40/0.60  thf('54', plain,
% 0.40/0.60      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.40/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['48', '53'])).
% 0.40/0.60  thf('55', plain,
% 0.40/0.60      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.40/0.60          = (sk_B)))
% 0.40/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('demod', [status(thm)], ['47', '54'])).
% 0.40/0.60  thf('56', plain,
% 0.40/0.60      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.40/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['32', '55'])).
% 0.40/0.60  thf('57', plain,
% 0.40/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(t52_pre_topc, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( l1_pre_topc @ A ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.60           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.40/0.60             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.40/0.60               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.40/0.60  thf('58', plain,
% 0.40/0.60      (![X27 : $i, X28 : $i]:
% 0.40/0.60         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.40/0.60          | ~ (v2_pre_topc @ X28)
% 0.40/0.60          | ((k2_pre_topc @ X28 @ X27) != (X27))
% 0.40/0.60          | (v4_pre_topc @ X27 @ X28)
% 0.40/0.60          | ~ (l1_pre_topc @ X28))),
% 0.40/0.60      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.40/0.60  thf('59', plain,
% 0.40/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.40/0.60        | (v4_pre_topc @ sk_B @ sk_A)
% 0.40/0.60        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.40/0.60        | ~ (v2_pre_topc @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['57', '58'])).
% 0.40/0.60  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('62', plain,
% 0.40/0.60      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.40/0.60      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.40/0.60  thf('63', plain,
% 0.40/0.60      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.40/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['56', '62'])).
% 0.40/0.60  thf('64', plain,
% 0.40/0.60      (((v4_pre_topc @ sk_B @ sk_A))
% 0.40/0.60         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('simplify', [status(thm)], ['63'])).
% 0.40/0.60  thf('65', plain,
% 0.40/0.60      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.60      inference('split', [status(esa)], ['26'])).
% 0.40/0.60  thf('66', plain,
% 0.40/0.60      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.40/0.60       ~
% 0.40/0.60       (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['64', '65'])).
% 0.40/0.60  thf('67', plain,
% 0.40/0.60      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.40/0.60       (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.40/0.60      inference('split', [status(esa)], ['16'])).
% 0.40/0.60  thf('68', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.40/0.60      inference('sat_resolution*', [status(thm)], ['27', '66', '67'])).
% 0.40/0.60  thf('69', plain,
% 0.40/0.60      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.40/0.60      inference('simpl_trail', [status(thm)], ['25', '68'])).
% 0.40/0.60  thf(involutiveness_k3_subset_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.60       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.40/0.60  thf('70', plain,
% 0.40/0.60      (![X16 : $i, X17 : $i]:
% 0.40/0.60         (((k3_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X16)) = (X16))
% 0.40/0.60          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.40/0.60      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.40/0.60  thf('71', plain,
% 0.40/0.60      (((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.40/0.60         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.40/0.60      inference('sup-', [status(thm)], ['69', '70'])).
% 0.40/0.60  thf('72', plain,
% 0.40/0.60      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.40/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.40/0.60  thf('73', plain,
% 0.40/0.60      (![X12 : $i, X13 : $i]:
% 0.40/0.60         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 0.40/0.60          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.40/0.60  thf('74', plain,
% 0.40/0.60      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.40/0.60          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.40/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['72', '73'])).
% 0.40/0.60  thf('75', plain,
% 0.40/0.60      (((k1_tops_1 @ sk_A @ sk_B)
% 0.40/0.60         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.60      inference('demod', [status(thm)], ['2', '3', '6'])).
% 0.40/0.60  thf('76', plain,
% 0.40/0.60      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.40/0.60          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.40/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.40/0.60      inference('demod', [status(thm)], ['74', '75'])).
% 0.40/0.60  thf('77', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.40/0.60      inference('sat_resolution*', [status(thm)], ['27', '66', '67'])).
% 0.40/0.60  thf('78', plain,
% 0.40/0.60      (((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.40/0.60         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.40/0.60      inference('simpl_trail', [status(thm)], ['76', '77'])).
% 0.40/0.60  thf('79', plain,
% 0.40/0.60      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.40/0.60         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.40/0.60      inference('demod', [status(thm)], ['71', '78'])).
% 0.40/0.60  thf('80', plain,
% 0.40/0.60      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.40/0.60         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.40/0.60      inference('sup+', [status(thm)], ['15', '79'])).
% 0.40/0.60  thf('81', plain,
% 0.40/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60              (k1_tops_1 @ sk_A @ sk_B))))
% 0.40/0.60         <= (~
% 0.40/0.60             (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('split', [status(esa)], ['26'])).
% 0.40/0.60  thf('82', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.40/0.60           = (k4_xboole_0 @ sk_B @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.60  thf('83', plain,
% 0.40/0.60      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.40/0.60         <= (~
% 0.40/0.60             (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.40/0.60      inference('demod', [status(thm)], ['81', '82'])).
% 0.40/0.60  thf('84', plain,
% 0.40/0.60      (~
% 0.40/0.60       (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.40/0.60             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.40/0.60      inference('sat_resolution*', [status(thm)], ['27', '66'])).
% 0.40/0.60  thf('85', plain,
% 0.40/0.60      (((k2_tops_1 @ sk_A @ sk_B)
% 0.40/0.60         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.40/0.60      inference('simpl_trail', [status(thm)], ['83', '84'])).
% 0.40/0.60  thf('86', plain, ($false),
% 0.40/0.60      inference('simplify_reflect-', [status(thm)], ['80', '85'])).
% 0.40/0.60  
% 0.40/0.60  % SZS output end Refutation
% 0.40/0.60  
% 0.40/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
