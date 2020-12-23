%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1578+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I8bXzvEKWq

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:49 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 268 expanded)
%              Number of leaves         :   30 (  91 expanded)
%              Depth                    :   25
%              Number of atoms          : 1128 (3322 expanded)
%              Number of equality atoms :   37 (  99 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_yellow_0_type,type,(
    v4_yellow_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(k1_toler_1_type,type,(
    k1_toler_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t57_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_yellow_0 @ ( g1_orders_2 @ B @ ( k1_toler_1 @ ( u1_orders_2 @ A ) @ B ) ) @ A )
            & ( m1_yellow_0 @ ( g1_orders_2 @ B @ ( k1_toler_1 @ ( u1_orders_2 @ A ) @ B ) ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_yellow_0 @ ( g1_orders_2 @ B @ ( k1_toler_1 @ ( u1_orders_2 @ A ) @ B ) ) @ A )
              & ( m1_yellow_0 @ ( g1_orders_2 @ B @ ( k1_toler_1 @ ( u1_orders_2 @ A ) @ B ) ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_yellow_0])).

thf('0',plain,
    ( ~ ( v4_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ~ ( m1_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v4_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A )
   <= ~ ( v4_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d6_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k2_wellord1 @ A @ B )
          = ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ B @ B ) ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_wellord1 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ ( k2_zfmisc_1 @ X9 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d6_wellord1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_wellord1 @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(redefinition_k1_toler_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k1_toler_1 @ A @ B )
        = ( k2_wellord1 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( ( k1_toler_1 @ X19 @ X20 )
        = ( k2_wellord1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_toler_1])).

thf(dt_k1_toler_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( m1_subset_1 @ ( k1_toler_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ B ) ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( m1_subset_1 @ ( k1_toler_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_toler_1])).

thf(dt_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ( ( v1_orders_2 @ ( g1_orders_2 @ A @ B ) )
        & ( l1_orders_2 @ ( g1_orders_2 @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( l1_orders_2 @ ( g1_orders_2 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_orders_2])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( l1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( m1_subset_1 @ ( k1_toler_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_toler_1])).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_orders_2 @ ( g1_orders_2 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_orders_2])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(abstractness_v1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ A )
       => ( A
          = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ X0 )
      | ( X0
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf('19',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( ( g1_orders_2 @ X17 @ X18 )
       != ( g1_orders_2 @ X15 @ X16 ) )
      | ( X18 = X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_orders_2 @ X2 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_orders_2 @ ( g1_orders_2 @ X2 @ X1 ) )
        = X1 )
      | ~ ( v1_orders_2 @ ( g1_orders_2 @ X2 @ X1 ) )
      | ~ ( l1_orders_2 @ ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( l1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) )
      | ( ( u1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) )
        = ( k1_toler_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( l1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) )
        = ( k1_toler_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ X0 )
      | ( X0
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf('29',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( ( g1_orders_2 @ X17 @ X18 )
       != ( g1_orders_2 @ X15 @ X16 ) )
      | ( X17 = X15 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_orders_2 @ X2 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_orders_2 @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_orders_2 @ ( g1_orders_2 @ X2 @ X1 ) )
      | ~ ( l1_orders_2 @ ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( l1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) )
      | ( ( u1_struct_0 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( l1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) )
        = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf(d13_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( m1_yellow_0 @ B @ A )
          <=> ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
              & ( r1_tarski @ ( u1_orders_2 @ B ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_orders_2 @ X4 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_tarski @ ( u1_orders_2 @ X4 ) @ ( u1_orders_2 @ X5 ) )
      | ( m1_yellow_0 @ X4 @ X5 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( l1_orders_2 @ X1 )
      | ( m1_yellow_0 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X2 @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ ( u1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X2 @ X0 ) ) ) @ ( u1_orders_2 @ X1 ) )
      | ~ ( l1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_toler_1 @ X1 @ X0 ) @ ( u1_orders_2 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( l1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) )
      | ( m1_yellow_0 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['26','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ( m1_yellow_0 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( l1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_toler_1 @ X1 @ X0 ) @ ( u1_orders_2 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_toler_1 @ X1 @ X0 ) @ ( u1_orders_2 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( m1_yellow_0 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['14','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ( m1_yellow_0 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ ( k1_toler_1 @ X1 @ X0 ) @ ( u1_orders_2 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_wellord1 @ X1 @ X0 ) @ ( u1_orders_2 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( m1_yellow_0 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['11','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_orders_2 @ X2 )
      | ( m1_yellow_0 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k2_wellord1 @ X1 @ X0 ) @ ( u1_orders_2 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( m1_yellow_0 @ ( g1_orders_2 @ X1 @ ( k1_toler_1 @ ( u1_orders_2 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( m1_yellow_0 @ ( g1_orders_2 @ X1 @ ( k1_toler_1 @ ( u1_orders_2 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( m1_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','46'])).

thf('48',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( m1_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( m1_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','49'])).

thf('51',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( m1_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A )
   <= ~ ( m1_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,(
    m1_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v4_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ~ ( m1_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,(
    ~ ( v4_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v4_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('59',plain,(
    m1_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['50','51'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) )
        = ( k1_toler_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) )
        = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf(d14_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
         => ( ( v4_yellow_0 @ B @ A )
          <=> ( ( u1_orders_2 @ B )
              = ( k1_toler_1 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('62',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_yellow_0 @ X6 @ X7 )
      | ( ( u1_orders_2 @ X6 )
       != ( k1_toler_1 @ ( u1_orders_2 @ X7 ) @ ( u1_struct_0 @ X6 ) ) )
      | ( v4_yellow_0 @ X6 @ X7 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d14_yellow_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( u1_orders_2 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) )
       != ( k1_toler_1 @ ( u1_orders_2 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( l1_orders_2 @ X2 )
      | ( v4_yellow_0 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( m1_yellow_0 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_toler_1 @ X1 @ X0 )
       != ( k1_toler_1 @ ( u1_orders_2 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( m1_yellow_0 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) @ X2 )
      | ( v4_yellow_0 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( l1_orders_2 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X2 )
      | ( v4_yellow_0 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( m1_yellow_0 @ ( g1_orders_2 @ X0 @ ( k1_toler_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_toler_1 @ X1 @ X0 )
       != ( k1_toler_1 @ ( u1_orders_2 @ X2 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
     != ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( v4_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B )
     != ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( v4_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( v4_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v4_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['58','69'])).

thf('71',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v4_yellow_0 @ ( g1_orders_2 @ sk_B @ ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['57','72'])).


%------------------------------------------------------------------------------
