%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e2kxSii0wi

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:37 EST 2020

% Result     : Theorem 0.63s
% Output     : Refutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 538 expanded)
%              Number of leaves         :   46 ( 180 expanded)
%              Depth                    :   16
%              Number of atoms          : 1685 (6153 expanded)
%              Number of equality atoms :  136 ( 439 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( ( k1_tops_1 @ X49 @ X48 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X49 ) @ X48 @ ( k2_tops_1 @ X49 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( ( k7_subset_1 @ X31 @ X30 @ X32 )
        = ( k4_xboole_0 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k6_subset_1 @ X28 @ X29 )
      = ( k4_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( ( k7_subset_1 @ X31 @ X30 @ X32 )
        = ( k6_subset_1 @ X30 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','10'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k6_subset_1 @ X28 @ X29 )
      = ( k4_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k6_subset_1 @ X28 @ X29 )
      = ( k4_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ ( k6_subset_1 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('20',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X47 @ X46 ) @ X46 )
      | ~ ( v4_pre_topc @ X46 @ X47 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('26',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k6_subset_1 @ X28 @ X29 )
      = ( k4_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ ( k6_subset_1 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('30',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X37: $i,X39: $i] :
      ( ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( r1_tarski @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('35',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X24 @ ( k3_subset_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('39',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k6_subset_1 @ X28 @ X29 )
      = ( k4_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k6_subset_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('43',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('49',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k6_subset_1 @ X28 @ X29 )
      = ( k4_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X8 @ X9 ) @ X8 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X37: $i,X39: $i] :
      ( ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( r1_tarski @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k6_subset_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( X0
      = ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','55'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('58',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['30','56','61'])).

thf('63',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['16','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('65',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('70',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','10'])).

thf('71',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X8 @ X9 ) @ X8 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('72',plain,(
    ! [X37: $i,X39: $i] :
      ( ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( r1_tarski @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('76',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['17'])).

thf('77',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('79',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('80',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k4_subset_1 @ X26 @ X25 @ X27 )
        = ( k2_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
          = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf('83',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('84',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['82','87'])).

thf('89',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('90',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k4_subset_1 @ X33 @ X34 @ ( k3_subset_1 @ X33 @ X34 ) )
        = ( k2_subset_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('91',plain,(
    ! [X18: $i] :
      ( ( k2_subset_1 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('92',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k4_subset_1 @ X33 @ X34 @ ( k3_subset_1 @ X33 @ X34 ) )
        = X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('95',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k6_subset_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('96',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','10'])).

thf('98',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k4_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['93','98'])).

thf('100',plain,
    ( ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['88','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('102',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('107',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( l1_pre_topc @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X42 @ X43 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('108',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k4_subset_1 @ X26 @ X25 @ X27 )
        = ( k2_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('116',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( ( k2_pre_topc @ X45 @ X44 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X45 ) @ X44 @ ( k2_tops_1 @ X45 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('117',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['114','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('122',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['104','105','120','121'])).

thf('123',plain,
    ( ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['88','99'])).

thf('124',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
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

thf('126',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( v2_pre_topc @ X41 )
      | ( ( k2_pre_topc @ X41 @ X40 )
       != X40 )
      | ( v4_pre_topc @ X40 @ X41 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('127',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['124','130'])).

thf('132',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('134',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','68','69','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e2kxSii0wi
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.63/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.63/0.82  % Solved by: fo/fo7.sh
% 0.63/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.63/0.82  % done 1221 iterations in 0.362s
% 0.63/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.63/0.82  % SZS output start Refutation
% 0.63/0.82  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.63/0.82  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.63/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.63/0.82  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.63/0.82  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.63/0.82  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.63/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.63/0.82  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.63/0.82  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.63/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.63/0.82  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.63/0.82  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.63/0.82  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.63/0.82  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.63/0.82  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.63/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.63/0.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.63/0.82  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.63/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.63/0.82  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.63/0.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.63/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.63/0.82  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.63/0.82  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.63/0.82  thf(t77_tops_1, conjecture,
% 0.63/0.82    (![A:$i]:
% 0.63/0.82     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.63/0.82       ( ![B:$i]:
% 0.63/0.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.82           ( ( v4_pre_topc @ B @ A ) <=>
% 0.63/0.82             ( ( k2_tops_1 @ A @ B ) =
% 0.63/0.82               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.63/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.63/0.82    (~( ![A:$i]:
% 0.63/0.82        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.63/0.82          ( ![B:$i]:
% 0.63/0.82            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.82              ( ( v4_pre_topc @ B @ A ) <=>
% 0.63/0.82                ( ( k2_tops_1 @ A @ B ) =
% 0.63/0.82                  ( k7_subset_1 @
% 0.63/0.82                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.63/0.82    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.63/0.82  thf('0', plain,
% 0.63/0.82      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82              (k1_tops_1 @ sk_A @ sk_B)))
% 0.63/0.82        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('1', plain,
% 0.63/0.82      (~
% 0.63/0.82       (((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.63/0.82       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.63/0.82      inference('split', [status(esa)], ['0'])).
% 0.63/0.82  thf('2', plain,
% 0.63/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf(t74_tops_1, axiom,
% 0.63/0.82    (![A:$i]:
% 0.63/0.82     ( ( l1_pre_topc @ A ) =>
% 0.63/0.82       ( ![B:$i]:
% 0.63/0.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.82           ( ( k1_tops_1 @ A @ B ) =
% 0.63/0.82             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.63/0.82  thf('3', plain,
% 0.63/0.82      (![X48 : $i, X49 : $i]:
% 0.63/0.82         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.63/0.82          | ((k1_tops_1 @ X49 @ X48)
% 0.63/0.82              = (k7_subset_1 @ (u1_struct_0 @ X49) @ X48 @ 
% 0.63/0.82                 (k2_tops_1 @ X49 @ X48)))
% 0.63/0.82          | ~ (l1_pre_topc @ X49))),
% 0.63/0.82      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.63/0.82  thf('4', plain,
% 0.63/0.82      ((~ (l1_pre_topc @ sk_A)
% 0.63/0.82        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.63/0.82            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.63/0.82      inference('sup-', [status(thm)], ['2', '3'])).
% 0.63/0.82  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('6', plain,
% 0.63/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf(redefinition_k7_subset_1, axiom,
% 0.63/0.82    (![A:$i,B:$i,C:$i]:
% 0.63/0.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.63/0.82       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.63/0.82  thf('7', plain,
% 0.63/0.82      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.63/0.82         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 0.63/0.82          | ((k7_subset_1 @ X31 @ X30 @ X32) = (k4_xboole_0 @ X30 @ X32)))),
% 0.63/0.82      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.63/0.82  thf(redefinition_k6_subset_1, axiom,
% 0.63/0.82    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.63/0.82  thf('8', plain,
% 0.63/0.82      (![X28 : $i, X29 : $i]:
% 0.63/0.82         ((k6_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))),
% 0.63/0.82      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.63/0.82  thf('9', plain,
% 0.63/0.82      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.63/0.82         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 0.63/0.82          | ((k7_subset_1 @ X31 @ X30 @ X32) = (k6_subset_1 @ X30 @ X32)))),
% 0.63/0.82      inference('demod', [status(thm)], ['7', '8'])).
% 0.63/0.82  thf('10', plain,
% 0.63/0.82      (![X0 : $i]:
% 0.63/0.82         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.63/0.82           = (k6_subset_1 @ sk_B @ X0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['6', '9'])).
% 0.63/0.82  thf('11', plain,
% 0.63/0.82      (((k1_tops_1 @ sk_A @ sk_B)
% 0.63/0.82         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.63/0.82      inference('demod', [status(thm)], ['4', '5', '10'])).
% 0.63/0.82  thf(t48_xboole_1, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.63/0.82  thf('12', plain,
% 0.63/0.82      (![X10 : $i, X11 : $i]:
% 0.63/0.82         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.63/0.82           = (k3_xboole_0 @ X10 @ X11))),
% 0.63/0.82      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.63/0.82  thf('13', plain,
% 0.63/0.82      (![X28 : $i, X29 : $i]:
% 0.63/0.82         ((k6_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))),
% 0.63/0.82      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.63/0.82  thf('14', plain,
% 0.63/0.82      (![X28 : $i, X29 : $i]:
% 0.63/0.82         ((k6_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))),
% 0.63/0.82      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.63/0.82  thf('15', plain,
% 0.63/0.82      (![X10 : $i, X11 : $i]:
% 0.63/0.82         ((k6_subset_1 @ X10 @ (k6_subset_1 @ X10 @ X11))
% 0.63/0.82           = (k3_xboole_0 @ X10 @ X11))),
% 0.63/0.82      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.63/0.82  thf('16', plain,
% 0.63/0.82      (((k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.63/0.82         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.63/0.82      inference('sup+', [status(thm)], ['11', '15'])).
% 0.63/0.82  thf('17', plain,
% 0.63/0.82      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82             (k1_tops_1 @ sk_A @ sk_B)))
% 0.63/0.82        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('18', plain,
% 0.63/0.82      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.63/0.82      inference('split', [status(esa)], ['17'])).
% 0.63/0.82  thf('19', plain,
% 0.63/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf(t69_tops_1, axiom,
% 0.63/0.82    (![A:$i]:
% 0.63/0.82     ( ( l1_pre_topc @ A ) =>
% 0.63/0.82       ( ![B:$i]:
% 0.63/0.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.82           ( ( v4_pre_topc @ B @ A ) =>
% 0.63/0.82             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.63/0.82  thf('20', plain,
% 0.63/0.82      (![X46 : $i, X47 : $i]:
% 0.63/0.82         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 0.63/0.82          | (r1_tarski @ (k2_tops_1 @ X47 @ X46) @ X46)
% 0.63/0.82          | ~ (v4_pre_topc @ X46 @ X47)
% 0.63/0.82          | ~ (l1_pre_topc @ X47))),
% 0.63/0.82      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.63/0.82  thf('21', plain,
% 0.63/0.82      ((~ (l1_pre_topc @ sk_A)
% 0.63/0.82        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.63/0.82        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.63/0.82      inference('sup-', [status(thm)], ['19', '20'])).
% 0.63/0.82  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('23', plain,
% 0.63/0.82      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.63/0.82        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.63/0.82      inference('demod', [status(thm)], ['21', '22'])).
% 0.63/0.82  thf('24', plain,
% 0.63/0.82      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.63/0.82         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['18', '23'])).
% 0.63/0.82  thf(l32_xboole_1, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.63/0.82  thf('25', plain,
% 0.63/0.82      (![X3 : $i, X5 : $i]:
% 0.63/0.82         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.63/0.82      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.63/0.82  thf('26', plain,
% 0.63/0.82      (![X28 : $i, X29 : $i]:
% 0.63/0.82         ((k6_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))),
% 0.63/0.82      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.63/0.82  thf('27', plain,
% 0.63/0.82      (![X3 : $i, X5 : $i]:
% 0.63/0.82         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.63/0.82      inference('demod', [status(thm)], ['25', '26'])).
% 0.63/0.82  thf('28', plain,
% 0.63/0.82      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.63/0.82         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['24', '27'])).
% 0.63/0.82  thf('29', plain,
% 0.63/0.82      (![X10 : $i, X11 : $i]:
% 0.63/0.82         ((k6_subset_1 @ X10 @ (k6_subset_1 @ X10 @ X11))
% 0.63/0.82           = (k3_xboole_0 @ X10 @ X11))),
% 0.63/0.82      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.63/0.82  thf('30', plain,
% 0.63/0.82      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.63/0.82          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 0.63/0.82         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.63/0.82      inference('sup+', [status(thm)], ['28', '29'])).
% 0.63/0.82  thf(d10_xboole_0, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.63/0.82  thf('31', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.63/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.63/0.82  thf('32', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.63/0.82      inference('simplify', [status(thm)], ['31'])).
% 0.63/0.82  thf(t3_subset, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.63/0.82  thf('33', plain,
% 0.63/0.82      (![X37 : $i, X39 : $i]:
% 0.63/0.82         ((m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X39)) | ~ (r1_tarski @ X37 @ X39))),
% 0.63/0.82      inference('cnf', [status(esa)], [t3_subset])).
% 0.63/0.82  thf('34', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['32', '33'])).
% 0.63/0.82  thf(involutiveness_k3_subset_1, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.63/0.82       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.63/0.82  thf('35', plain,
% 0.63/0.82      (![X23 : $i, X24 : $i]:
% 0.63/0.82         (((k3_subset_1 @ X24 @ (k3_subset_1 @ X24 @ X23)) = (X23))
% 0.63/0.82          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.63/0.82      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.63/0.82  thf('36', plain,
% 0.63/0.82      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['34', '35'])).
% 0.63/0.82  thf('37', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['32', '33'])).
% 0.63/0.82  thf(d5_subset_1, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.63/0.82       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.63/0.82  thf('38', plain,
% 0.63/0.82      (![X19 : $i, X20 : $i]:
% 0.63/0.82         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.63/0.82          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.63/0.82      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.63/0.82  thf('39', plain,
% 0.63/0.82      (![X28 : $i, X29 : $i]:
% 0.63/0.82         ((k6_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))),
% 0.63/0.82      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.63/0.82  thf('40', plain,
% 0.63/0.82      (![X19 : $i, X20 : $i]:
% 0.63/0.82         (((k3_subset_1 @ X19 @ X20) = (k6_subset_1 @ X19 @ X20))
% 0.63/0.82          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.63/0.82      inference('demod', [status(thm)], ['38', '39'])).
% 0.63/0.82  thf('41', plain,
% 0.63/0.82      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k6_subset_1 @ X0 @ X0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['37', '40'])).
% 0.63/0.82  thf('42', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.63/0.82      inference('simplify', [status(thm)], ['31'])).
% 0.63/0.82  thf('43', plain,
% 0.63/0.82      (![X3 : $i, X5 : $i]:
% 0.63/0.82         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.63/0.82      inference('demod', [status(thm)], ['25', '26'])).
% 0.63/0.82  thf('44', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['42', '43'])).
% 0.63/0.82  thf('45', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.63/0.82      inference('demod', [status(thm)], ['41', '44'])).
% 0.63/0.82  thf('46', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.63/0.82      inference('demod', [status(thm)], ['36', '45'])).
% 0.63/0.82  thf('47', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['42', '43'])).
% 0.63/0.82  thf(t36_xboole_1, axiom,
% 0.63/0.82    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.63/0.82  thf('48', plain,
% 0.63/0.82      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.63/0.82      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.63/0.82  thf('49', plain,
% 0.63/0.82      (![X28 : $i, X29 : $i]:
% 0.63/0.82         ((k6_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))),
% 0.63/0.82      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.63/0.82  thf('50', plain,
% 0.63/0.82      (![X8 : $i, X9 : $i]: (r1_tarski @ (k6_subset_1 @ X8 @ X9) @ X8)),
% 0.63/0.82      inference('demod', [status(thm)], ['48', '49'])).
% 0.63/0.82  thf('51', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.63/0.82      inference('sup+', [status(thm)], ['47', '50'])).
% 0.63/0.82  thf('52', plain,
% 0.63/0.82      (![X37 : $i, X39 : $i]:
% 0.63/0.82         ((m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X39)) | ~ (r1_tarski @ X37 @ X39))),
% 0.63/0.82      inference('cnf', [status(esa)], [t3_subset])).
% 0.63/0.82  thf('53', plain,
% 0.63/0.82      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['51', '52'])).
% 0.63/0.82  thf('54', plain,
% 0.63/0.82      (![X19 : $i, X20 : $i]:
% 0.63/0.82         (((k3_subset_1 @ X19 @ X20) = (k6_subset_1 @ X19 @ X20))
% 0.63/0.82          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.63/0.82      inference('demod', [status(thm)], ['38', '39'])).
% 0.63/0.82  thf('55', plain,
% 0.63/0.82      (![X0 : $i]:
% 0.63/0.82         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k6_subset_1 @ X0 @ k1_xboole_0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['53', '54'])).
% 0.63/0.82  thf('56', plain, (![X0 : $i]: ((X0) = (k6_subset_1 @ X0 @ k1_xboole_0))),
% 0.63/0.82      inference('sup+', [status(thm)], ['46', '55'])).
% 0.63/0.82  thf(commutativity_k2_tarski, axiom,
% 0.63/0.82    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.63/0.82  thf('57', plain,
% 0.63/0.82      (![X14 : $i, X15 : $i]:
% 0.63/0.82         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 0.63/0.82      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.63/0.82  thf(t12_setfam_1, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.63/0.82  thf('58', plain,
% 0.63/0.82      (![X35 : $i, X36 : $i]:
% 0.63/0.82         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.63/0.82      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.63/0.82  thf('59', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]:
% 0.63/0.82         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.63/0.82      inference('sup+', [status(thm)], ['57', '58'])).
% 0.63/0.82  thf('60', plain,
% 0.63/0.82      (![X35 : $i, X36 : $i]:
% 0.63/0.82         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.63/0.82      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.63/0.82  thf('61', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.63/0.82      inference('sup+', [status(thm)], ['59', '60'])).
% 0.63/0.82  thf('62', plain,
% 0.63/0.82      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.63/0.82         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.63/0.82      inference('demod', [status(thm)], ['30', '56', '61'])).
% 0.63/0.82  thf('63', plain,
% 0.63/0.82      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.63/0.82         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.63/0.82      inference('sup+', [status(thm)], ['16', '62'])).
% 0.63/0.82  thf('64', plain,
% 0.63/0.82      (![X0 : $i]:
% 0.63/0.82         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.63/0.82           = (k6_subset_1 @ sk_B @ X0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['6', '9'])).
% 0.63/0.82  thf('65', plain,
% 0.63/0.82      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82              (k1_tops_1 @ sk_A @ sk_B))))
% 0.63/0.82         <= (~
% 0.63/0.82             (((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('split', [status(esa)], ['0'])).
% 0.63/0.82  thf('66', plain,
% 0.63/0.82      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.63/0.82         <= (~
% 0.63/0.82             (((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('sup-', [status(thm)], ['64', '65'])).
% 0.63/0.82  thf('67', plain,
% 0.63/0.82      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.63/0.82         <= (~
% 0.63/0.82             (((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.63/0.82             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['63', '66'])).
% 0.63/0.82  thf('68', plain,
% 0.63/0.82      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.63/0.82       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.63/0.82      inference('simplify', [status(thm)], ['67'])).
% 0.63/0.82  thf('69', plain,
% 0.63/0.82      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.63/0.82       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.63/0.82      inference('split', [status(esa)], ['17'])).
% 0.63/0.82  thf('70', plain,
% 0.63/0.82      (((k1_tops_1 @ sk_A @ sk_B)
% 0.63/0.82         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.63/0.82      inference('demod', [status(thm)], ['4', '5', '10'])).
% 0.63/0.82  thf('71', plain,
% 0.63/0.82      (![X8 : $i, X9 : $i]: (r1_tarski @ (k6_subset_1 @ X8 @ X9) @ X8)),
% 0.63/0.82      inference('demod', [status(thm)], ['48', '49'])).
% 0.63/0.82  thf('72', plain,
% 0.63/0.82      (![X37 : $i, X39 : $i]:
% 0.63/0.82         ((m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X39)) | ~ (r1_tarski @ X37 @ X39))),
% 0.63/0.82      inference('cnf', [status(esa)], [t3_subset])).
% 0.63/0.82  thf('73', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]:
% 0.63/0.82         (m1_subset_1 @ (k6_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['71', '72'])).
% 0.63/0.82  thf('74', plain,
% 0.63/0.82      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.63/0.82      inference('sup+', [status(thm)], ['70', '73'])).
% 0.63/0.82  thf('75', plain,
% 0.63/0.82      (![X0 : $i]:
% 0.63/0.82         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.63/0.82           = (k6_subset_1 @ sk_B @ X0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['6', '9'])).
% 0.63/0.82  thf('76', plain,
% 0.63/0.82      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82             (k1_tops_1 @ sk_A @ sk_B))))
% 0.63/0.82         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('split', [status(esa)], ['17'])).
% 0.63/0.82  thf('77', plain,
% 0.63/0.82      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.63/0.82         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('sup+', [status(thm)], ['75', '76'])).
% 0.63/0.82  thf('78', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]:
% 0.63/0.82         (m1_subset_1 @ (k6_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.63/0.82      inference('sup-', [status(thm)], ['71', '72'])).
% 0.63/0.82  thf('79', plain,
% 0.63/0.82      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.63/0.82         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('sup+', [status(thm)], ['77', '78'])).
% 0.63/0.82  thf(redefinition_k4_subset_1, axiom,
% 0.63/0.82    (![A:$i,B:$i,C:$i]:
% 0.63/0.82     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.63/0.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.63/0.82       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.63/0.82  thf('80', plain,
% 0.63/0.82      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.63/0.82         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.63/0.82          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26))
% 0.63/0.82          | ((k4_subset_1 @ X26 @ X25 @ X27) = (k2_xboole_0 @ X25 @ X27)))),
% 0.63/0.82      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.63/0.82  thf('81', plain,
% 0.63/0.82      ((![X0 : $i]:
% 0.63/0.82          (((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.63/0.82             = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 0.63/0.82           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))))
% 0.63/0.82         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('sup-', [status(thm)], ['79', '80'])).
% 0.63/0.82  thf('82', plain,
% 0.63/0.82      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.63/0.82          (k1_tops_1 @ sk_A @ sk_B))
% 0.63/0.82          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.63/0.82             (k1_tops_1 @ sk_A @ sk_B))))
% 0.63/0.82         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('sup-', [status(thm)], ['74', '81'])).
% 0.63/0.82  thf('83', plain,
% 0.63/0.82      (![X14 : $i, X15 : $i]:
% 0.63/0.82         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 0.63/0.82      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.63/0.82  thf(l51_zfmisc_1, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.63/0.82  thf('84', plain,
% 0.63/0.82      (![X16 : $i, X17 : $i]:
% 0.63/0.82         ((k3_tarski @ (k2_tarski @ X16 @ X17)) = (k2_xboole_0 @ X16 @ X17))),
% 0.63/0.82      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.63/0.82  thf('85', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]:
% 0.63/0.82         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.63/0.82      inference('sup+', [status(thm)], ['83', '84'])).
% 0.63/0.82  thf('86', plain,
% 0.63/0.82      (![X16 : $i, X17 : $i]:
% 0.63/0.82         ((k3_tarski @ (k2_tarski @ X16 @ X17)) = (k2_xboole_0 @ X16 @ X17))),
% 0.63/0.82      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.63/0.82  thf('87', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.63/0.82      inference('sup+', [status(thm)], ['85', '86'])).
% 0.63/0.82  thf('88', plain,
% 0.63/0.82      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.63/0.82          (k1_tops_1 @ sk_A @ sk_B))
% 0.63/0.82          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.63/0.82             (k2_tops_1 @ sk_A @ sk_B))))
% 0.63/0.82         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('demod', [status(thm)], ['82', '87'])).
% 0.63/0.82  thf('89', plain,
% 0.63/0.82      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.63/0.82         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('sup+', [status(thm)], ['77', '78'])).
% 0.63/0.82  thf(t25_subset_1, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.63/0.82       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.63/0.82         ( k2_subset_1 @ A ) ) ))).
% 0.63/0.82  thf('90', plain,
% 0.63/0.82      (![X33 : $i, X34 : $i]:
% 0.63/0.82         (((k4_subset_1 @ X33 @ X34 @ (k3_subset_1 @ X33 @ X34))
% 0.63/0.82            = (k2_subset_1 @ X33))
% 0.63/0.82          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 0.63/0.82      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.63/0.82  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.63/0.82  thf('91', plain, (![X18 : $i]: ((k2_subset_1 @ X18) = (X18))),
% 0.63/0.82      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.63/0.82  thf('92', plain,
% 0.63/0.82      (![X33 : $i, X34 : $i]:
% 0.63/0.82         (((k4_subset_1 @ X33 @ X34 @ (k3_subset_1 @ X33 @ X34)) = (X33))
% 0.63/0.82          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 0.63/0.82      inference('demod', [status(thm)], ['90', '91'])).
% 0.63/0.82  thf('93', plain,
% 0.63/0.82      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.63/0.82          (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B)))
% 0.63/0.82         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('sup-', [status(thm)], ['89', '92'])).
% 0.63/0.82  thf('94', plain,
% 0.63/0.82      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.63/0.82         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('sup+', [status(thm)], ['77', '78'])).
% 0.63/0.82  thf('95', plain,
% 0.63/0.82      (![X19 : $i, X20 : $i]:
% 0.63/0.82         (((k3_subset_1 @ X19 @ X20) = (k6_subset_1 @ X19 @ X20))
% 0.63/0.82          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.63/0.82      inference('demod', [status(thm)], ['38', '39'])).
% 0.63/0.82  thf('96', plain,
% 0.63/0.82      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.63/0.82          = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.63/0.82         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('sup-', [status(thm)], ['94', '95'])).
% 0.63/0.82  thf('97', plain,
% 0.63/0.82      (((k1_tops_1 @ sk_A @ sk_B)
% 0.63/0.82         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.63/0.82      inference('demod', [status(thm)], ['4', '5', '10'])).
% 0.63/0.82  thf('98', plain,
% 0.63/0.82      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.63/0.82          = (k1_tops_1 @ sk_A @ sk_B)))
% 0.63/0.82         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('demod', [status(thm)], ['96', '97'])).
% 0.63/0.82  thf('99', plain,
% 0.63/0.82      ((((k4_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.63/0.82          (k1_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.63/0.82         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('demod', [status(thm)], ['93', '98'])).
% 0.63/0.82  thf('100', plain,
% 0.63/0.82      ((((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.63/0.82          = (sk_B)))
% 0.63/0.82         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('sup+', [status(thm)], ['88', '99'])).
% 0.63/0.82  thf('101', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.63/0.82      inference('sup+', [status(thm)], ['85', '86'])).
% 0.63/0.82  thf(t6_xboole_1, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.63/0.82  thf('102', plain,
% 0.63/0.82      (![X12 : $i, X13 : $i]:
% 0.63/0.82         ((k2_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13))
% 0.63/0.82           = (k2_xboole_0 @ X12 @ X13))),
% 0.63/0.82      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.63/0.82  thf('103', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]:
% 0.63/0.82         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.63/0.82           = (k2_xboole_0 @ X0 @ X1))),
% 0.63/0.82      inference('sup+', [status(thm)], ['101', '102'])).
% 0.63/0.82  thf('104', plain,
% 0.63/0.82      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.63/0.82          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.63/0.82             (k1_tops_1 @ sk_A @ sk_B))))
% 0.63/0.82         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('sup+', [status(thm)], ['100', '103'])).
% 0.63/0.82  thf('105', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.63/0.82      inference('sup+', [status(thm)], ['85', '86'])).
% 0.63/0.82  thf('106', plain,
% 0.63/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf(dt_k2_tops_1, axiom,
% 0.63/0.82    (![A:$i,B:$i]:
% 0.63/0.82     ( ( ( l1_pre_topc @ A ) & 
% 0.63/0.82         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.63/0.82       ( m1_subset_1 @
% 0.63/0.82         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.63/0.82  thf('107', plain,
% 0.63/0.82      (![X42 : $i, X43 : $i]:
% 0.63/0.82         (~ (l1_pre_topc @ X42)
% 0.63/0.82          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.63/0.82          | (m1_subset_1 @ (k2_tops_1 @ X42 @ X43) @ 
% 0.63/0.82             (k1_zfmisc_1 @ (u1_struct_0 @ X42))))),
% 0.63/0.82      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.63/0.82  thf('108', plain,
% 0.63/0.82      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.63/0.82         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.63/0.82        | ~ (l1_pre_topc @ sk_A))),
% 0.63/0.82      inference('sup-', [status(thm)], ['106', '107'])).
% 0.63/0.82  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('110', plain,
% 0.63/0.82      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.63/0.82        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('demod', [status(thm)], ['108', '109'])).
% 0.63/0.82  thf('111', plain,
% 0.63/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('112', plain,
% 0.63/0.82      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.63/0.82         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.63/0.82          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26))
% 0.63/0.82          | ((k4_subset_1 @ X26 @ X25 @ X27) = (k2_xboole_0 @ X25 @ X27)))),
% 0.63/0.82      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.63/0.82  thf('113', plain,
% 0.63/0.82      (![X0 : $i]:
% 0.63/0.82         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.63/0.82            = (k2_xboole_0 @ sk_B @ X0))
% 0.63/0.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.63/0.82      inference('sup-', [status(thm)], ['111', '112'])).
% 0.63/0.82  thf('114', plain,
% 0.63/0.82      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.63/0.82         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.63/0.82      inference('sup-', [status(thm)], ['110', '113'])).
% 0.63/0.82  thf('115', plain,
% 0.63/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf(t65_tops_1, axiom,
% 0.63/0.82    (![A:$i]:
% 0.63/0.82     ( ( l1_pre_topc @ A ) =>
% 0.63/0.82       ( ![B:$i]:
% 0.63/0.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.82           ( ( k2_pre_topc @ A @ B ) =
% 0.63/0.82             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.63/0.82  thf('116', plain,
% 0.63/0.82      (![X44 : $i, X45 : $i]:
% 0.63/0.82         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.63/0.82          | ((k2_pre_topc @ X45 @ X44)
% 0.63/0.82              = (k4_subset_1 @ (u1_struct_0 @ X45) @ X44 @ 
% 0.63/0.82                 (k2_tops_1 @ X45 @ X44)))
% 0.63/0.82          | ~ (l1_pre_topc @ X45))),
% 0.63/0.82      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.63/0.82  thf('117', plain,
% 0.63/0.82      ((~ (l1_pre_topc @ sk_A)
% 0.63/0.82        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.63/0.82            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.63/0.82      inference('sup-', [status(thm)], ['115', '116'])).
% 0.63/0.82  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('119', plain,
% 0.63/0.82      (((k2_pre_topc @ sk_A @ sk_B)
% 0.63/0.82         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.63/0.82      inference('demod', [status(thm)], ['117', '118'])).
% 0.63/0.82  thf('120', plain,
% 0.63/0.82      (((k2_pre_topc @ sk_A @ sk_B)
% 0.63/0.82         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.63/0.82      inference('sup+', [status(thm)], ['114', '119'])).
% 0.63/0.82  thf('121', plain,
% 0.63/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.63/0.82      inference('sup+', [status(thm)], ['85', '86'])).
% 0.63/0.82  thf('122', plain,
% 0.63/0.82      ((((k2_pre_topc @ sk_A @ sk_B)
% 0.63/0.82          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.63/0.82             (k2_tops_1 @ sk_A @ sk_B))))
% 0.63/0.82         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('demod', [status(thm)], ['104', '105', '120', '121'])).
% 0.63/0.82  thf('123', plain,
% 0.63/0.82      ((((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.63/0.82          = (sk_B)))
% 0.63/0.82         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('sup+', [status(thm)], ['88', '99'])).
% 0.63/0.82  thf('124', plain,
% 0.63/0.82      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.63/0.82         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('sup+', [status(thm)], ['122', '123'])).
% 0.63/0.82  thf('125', plain,
% 0.63/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf(t52_pre_topc, axiom,
% 0.63/0.82    (![A:$i]:
% 0.63/0.82     ( ( l1_pre_topc @ A ) =>
% 0.63/0.82       ( ![B:$i]:
% 0.63/0.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.63/0.82           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.63/0.82             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.63/0.82               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.63/0.82  thf('126', plain,
% 0.63/0.82      (![X40 : $i, X41 : $i]:
% 0.63/0.82         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.63/0.82          | ~ (v2_pre_topc @ X41)
% 0.63/0.82          | ((k2_pre_topc @ X41 @ X40) != (X40))
% 0.63/0.82          | (v4_pre_topc @ X40 @ X41)
% 0.63/0.82          | ~ (l1_pre_topc @ X41))),
% 0.63/0.82      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.63/0.82  thf('127', plain,
% 0.63/0.82      ((~ (l1_pre_topc @ sk_A)
% 0.63/0.82        | (v4_pre_topc @ sk_B @ sk_A)
% 0.63/0.82        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.63/0.82        | ~ (v2_pre_topc @ sk_A))),
% 0.63/0.82      inference('sup-', [status(thm)], ['125', '126'])).
% 0.63/0.82  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 0.63/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.82  thf('130', plain,
% 0.63/0.82      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.63/0.82      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.63/0.82  thf('131', plain,
% 0.63/0.82      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.63/0.82         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('sup-', [status(thm)], ['124', '130'])).
% 0.63/0.82  thf('132', plain,
% 0.63/0.82      (((v4_pre_topc @ sk_B @ sk_A))
% 0.63/0.82         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.63/0.82      inference('simplify', [status(thm)], ['131'])).
% 0.63/0.82  thf('133', plain,
% 0.63/0.82      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.63/0.82      inference('split', [status(esa)], ['0'])).
% 0.63/0.82  thf('134', plain,
% 0.63/0.82      (~
% 0.63/0.82       (((k2_tops_1 @ sk_A @ sk_B)
% 0.63/0.82          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.63/0.82             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.63/0.82       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.63/0.82      inference('sup-', [status(thm)], ['132', '133'])).
% 0.63/0.82  thf('135', plain, ($false),
% 0.63/0.82      inference('sat_resolution*', [status(thm)], ['1', '68', '69', '134'])).
% 0.63/0.82  
% 0.63/0.82  % SZS output end Refutation
% 0.63/0.82  
% 0.63/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
