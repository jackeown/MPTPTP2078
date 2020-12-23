%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZUtSdEKQJC

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 539 expanded)
%              Number of leaves         :   38 ( 177 expanded)
%              Depth                    :   18
%              Number of atoms          :  905 (7232 expanded)
%              Number of equality atoms :   17 ( 264 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_wellord1_type,type,(
    r2_wellord1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t87_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) )
           != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) )
             != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_orders_2])).

thf('0',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d17_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( C
                = ( k4_orders_2 @ A @ B ) )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ C )
                <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ~ ( m1_orders_1 @ X17 @ ( k1_orders_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( X19
       != ( k4_orders_2 @ X18 @ X17 ) )
      | ( m2_orders_2 @ X21 @ X18 @ X17 )
      | ~ ( r2_hidden @ X21 @ X19 )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('4',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( r2_hidden @ X21 @ ( k4_orders_2 @ X18 @ X17 ) )
      | ( m2_orders_2 @ X21 @ X18 @ X17 )
      | ~ ( m1_orders_1 @ X17 @ ( k1_orders_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6','7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( m2_orders_2 @ ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ~ ( v1_xboole_0 @ ( k4_orders_2 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_orders_2 @ X26 )
      | ~ ( v5_orders_2 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v3_orders_2 @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_orders_1 @ X27 @ ( k1_orders_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v1_xboole_0 @ ( k4_orders_2 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[fc9_orders_2])).

thf('16',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    m2_orders_2 @ ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['13','23'])).

thf('25',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m2_orders_2 @ C @ A @ B )
         => ( ( v6_orders_2 @ C @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( l1_orders_2 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_orders_1 @ X24 @ ( k1_orders_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m2_orders_2 @ X25 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf('36',plain,(
    m2_orders_2 @ ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['13','23'])).

thf('37',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_orders_1 @ X17 @ ( k1_orders_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( X19
       != ( k4_orders_2 @ X18 @ X17 ) )
      | ( r2_hidden @ X20 @ X19 )
      | ~ ( m2_orders_2 @ X20 @ X18 @ X17 )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('39',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( m2_orders_2 @ X20 @ X18 @ X17 )
      | ( r2_hidden @ X20 @ ( k4_orders_2 @ X18 @ X17 ) )
      | ~ ( m1_orders_1 @ X17 @ ( k1_orders_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    r2_hidden @ ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','47'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('49',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X7 ) @ X9 )
      | ~ ( r2_hidden @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('50',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ) @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X11 ) @ ( k3_tarski @ X12 ) )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('52',plain,(
    r1_tarski @ ( k3_tarski @ ( k1_tarski @ ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ) ) @ ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('53',plain,(
    ! [X10: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('54',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r1_tarski @ ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['52','53','54'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('56',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('57',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','59'])).

thf(d16_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ( v6_orders_2 @ C @ A )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( m2_orders_2 @ C @ A @ B )
              <=> ( ( C != k1_xboole_0 )
                  & ( r2_wellord1 @ ( u1_orders_2 @ A ) @ C )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_hidden @ D @ C )
                       => ( ( k1_funct_1 @ B @ ( k1_orders_2 @ A @ ( k3_orders_2 @ A @ C @ D ) ) )
                          = D ) ) ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_orders_1 @ X13 @ ( k1_orders_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m2_orders_2 @ X15 @ X14 @ X13 )
      | ( X15 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v6_orders_2 @ X15 @ X14 )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d16_orders_2])).

thf('62',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ X14 @ X13 )
      | ~ ( m1_orders_1 @ X13 @ ( k1_orders_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    m2_orders_2 @ ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['13','23'])).

thf('65',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( l1_orders_2 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_orders_1 @ X24 @ ( k1_orders_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v6_orders_2 @ X25 @ X23 )
      | ~ ( m2_orders_2 @ X25 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( v6_orders_2 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( v6_orders_2 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v6_orders_2 @ X0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    v6_orders_2 @ ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['64','74'])).

thf('76',plain,
    ( ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','58'])).

thf('77',plain,(
    v6_orders_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','77','78','79','80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','84'])).

thf('86',plain,(
    m2_orders_2 @ ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['13','23'])).

thf('87',plain,
    ( ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','58'])).

thf('88',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['85','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZUtSdEKQJC
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 119 iterations in 0.058s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.21/0.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.53  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.21/0.53  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.53  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.21/0.53  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.53  thf(r2_wellord1_type, type, r2_wellord1: $i > $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.53  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.21/0.53  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.53  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(t87_orders_2, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.53            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d1_xboole_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d17_orders_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.21/0.53         (~ (m1_orders_1 @ X17 @ (k1_orders_1 @ (u1_struct_0 @ X18)))
% 0.21/0.53          | ((X19) != (k4_orders_2 @ X18 @ X17))
% 0.21/0.53          | (m2_orders_2 @ X21 @ X18 @ X17)
% 0.21/0.53          | ~ (r2_hidden @ X21 @ X19)
% 0.21/0.53          | ~ (l1_orders_2 @ X18)
% 0.21/0.53          | ~ (v5_orders_2 @ X18)
% 0.21/0.53          | ~ (v4_orders_2 @ X18)
% 0.21/0.53          | ~ (v3_orders_2 @ X18)
% 0.21/0.53          | (v2_struct_0 @ X18))),
% 0.21/0.53      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i, X21 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X18)
% 0.21/0.53          | ~ (v3_orders_2 @ X18)
% 0.21/0.53          | ~ (v4_orders_2 @ X18)
% 0.21/0.53          | ~ (v5_orders_2 @ X18)
% 0.21/0.53          | ~ (l1_orders_2 @ X18)
% 0.21/0.53          | ~ (r2_hidden @ X21 @ (k4_orders_2 @ X18 @ X17))
% 0.21/0.53          | (m2_orders_2 @ X21 @ X18 @ X17)
% 0.21/0.53          | ~ (m1_orders_1 @ X17 @ (k1_orders_1 @ (u1_struct_0 @ X18))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.53  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('7', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('8', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.21/0.53  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.53          | (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.21/0.53      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (((v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.53        | (m2_orders_2 @ (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) @ sk_A @ sk_B_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '12'])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(fc9_orders_2, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.21/0.53         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.53       ( ~( v1_xboole_0 @ ( k4_orders_2 @ A @ B ) ) ) ))).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X26 : $i, X27 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ X26)
% 0.21/0.53          | ~ (v5_orders_2 @ X26)
% 0.21/0.53          | ~ (v4_orders_2 @ X26)
% 0.21/0.53          | ~ (v3_orders_2 @ X26)
% 0.21/0.53          | (v2_struct_0 @ X26)
% 0.21/0.53          | ~ (m1_orders_1 @ X27 @ (k1_orders_1 @ (u1_struct_0 @ X26)))
% 0.21/0.53          | ~ (v1_xboole_0 @ (k4_orders_2 @ X26 @ X27)))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc9_orders_2])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.53        | (v2_struct_0 @ sk_A)
% 0.21/0.53        | ~ (v3_orders_2 @ sk_A)
% 0.21/0.53        | ~ (v4_orders_2 @ sk_A)
% 0.21/0.53        | ~ (v5_orders_2 @ sk_A)
% 0.21/0.53        | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('17', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('18', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('19', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('20', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.21/0.53  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('23', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.21/0.53      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      ((m2_orders_2 @ (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) @ sk_A @ sk_B_1)),
% 0.21/0.53      inference('clc', [status(thm)], ['13', '23'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_m2_orders_2, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.21/0.53         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.53       ( ![C:$i]:
% 0.21/0.53         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.53           ( ( v6_orders_2 @ C @ A ) & 
% 0.21/0.53             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ X23)
% 0.21/0.53          | ~ (v5_orders_2 @ X23)
% 0.21/0.53          | ~ (v4_orders_2 @ X23)
% 0.21/0.53          | ~ (v3_orders_2 @ X23)
% 0.21/0.53          | (v2_struct_0 @ X23)
% 0.21/0.53          | ~ (m1_orders_1 @ X24 @ (k1_orders_1 @ (u1_struct_0 @ X23)))
% 0.21/0.53          | (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.53          | ~ (m2_orders_2 @ X25 @ X23 @ X24))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.53          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | (v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.53          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.53  thf('28', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('29', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('30', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('31', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.53          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.21/0.53  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.21/0.53      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      ((m1_subset_1 @ (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) @ 
% 0.21/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['24', '34'])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      ((m2_orders_2 @ (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) @ sk_A @ sk_B_1)),
% 0.21/0.53      inference('clc', [status(thm)], ['13', '23'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.53         (~ (m1_orders_1 @ X17 @ (k1_orders_1 @ (u1_struct_0 @ X18)))
% 0.21/0.53          | ((X19) != (k4_orders_2 @ X18 @ X17))
% 0.21/0.53          | (r2_hidden @ X20 @ X19)
% 0.21/0.53          | ~ (m2_orders_2 @ X20 @ X18 @ X17)
% 0.21/0.53          | ~ (l1_orders_2 @ X18)
% 0.21/0.53          | ~ (v5_orders_2 @ X18)
% 0.21/0.53          | ~ (v4_orders_2 @ X18)
% 0.21/0.53          | ~ (v3_orders_2 @ X18)
% 0.21/0.53          | (v2_struct_0 @ X18))),
% 0.21/0.53      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X18)
% 0.21/0.53          | ~ (v3_orders_2 @ X18)
% 0.21/0.53          | ~ (v4_orders_2 @ X18)
% 0.21/0.53          | ~ (v5_orders_2 @ X18)
% 0.21/0.53          | ~ (l1_orders_2 @ X18)
% 0.21/0.53          | ~ (m2_orders_2 @ X20 @ X18 @ X17)
% 0.21/0.53          | (r2_hidden @ X20 @ (k4_orders_2 @ X18 @ X17))
% 0.21/0.53          | ~ (m1_orders_1 @ X17 @ (k1_orders_1 @ (u1_struct_0 @ X18))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.53          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['37', '39'])).
% 0.21/0.53  thf('41', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('42', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('43', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('44', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.53          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 0.21/0.53  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.53          | (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.21/0.53      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      ((r2_hidden @ (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) @ 
% 0.21/0.53        (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['36', '47'])).
% 0.21/0.53  thf(l1_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (![X7 : $i, X9 : $i]:
% 0.21/0.53         ((r1_tarski @ (k1_tarski @ X7) @ X9) | ~ (r2_hidden @ X7 @ X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      ((r1_tarski @ (k1_tarski @ (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1))) @ 
% 0.21/0.53        (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.53  thf(t95_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.53       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i]:
% 0.21/0.53         ((r1_tarski @ (k3_tarski @ X11) @ (k3_tarski @ X12))
% 0.21/0.53          | ~ (r1_tarski @ X11 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      ((r1_tarski @ 
% 0.21/0.53        (k3_tarski @ (k1_tarski @ (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)))) @ 
% 0.21/0.53        (k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.53  thf(t31_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.21/0.53  thf('53', plain, (![X10 : $i]: ((k3_tarski @ (k1_tarski @ X10)) = (X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      ((r1_tarski @ (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) @ k1_xboole_0)),
% 0.21/0.53      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.21/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.53  thf('56', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      (![X3 : $i, X5 : $i]:
% 0.21/0.53         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.53  thf('59', plain, (((sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['55', '58'])).
% 0.21/0.53  thf('60', plain,
% 0.21/0.53      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['35', '59'])).
% 0.21/0.53  thf(d16_orders_2, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.53         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( v6_orders_2 @ C @ A ) & 
% 0.21/0.53                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.53               ( ( m2_orders_2 @ C @ A @ B ) <=>
% 0.21/0.53                 ( ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.53                   ( r2_wellord1 @ ( u1_orders_2 @ A ) @ C ) & 
% 0.21/0.53                   ( ![D:$i]:
% 0.21/0.53                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.53                       ( ( r2_hidden @ D @ C ) =>
% 0.21/0.53                         ( ( k1_funct_1 @
% 0.21/0.53                             B @ 
% 0.21/0.53                             ( k1_orders_2 @ A @ ( k3_orders_2 @ A @ C @ D ) ) ) =
% 0.21/0.53                           ( D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('61', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.53         (~ (m1_orders_1 @ X13 @ (k1_orders_1 @ (u1_struct_0 @ X14)))
% 0.21/0.53          | ~ (m2_orders_2 @ X15 @ X14 @ X13)
% 0.21/0.53          | ((X15) != (k1_xboole_0))
% 0.21/0.53          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.53          | ~ (v6_orders_2 @ X15 @ X14)
% 0.21/0.53          | ~ (l1_orders_2 @ X14)
% 0.21/0.53          | ~ (v5_orders_2 @ X14)
% 0.21/0.53          | ~ (v4_orders_2 @ X14)
% 0.21/0.53          | ~ (v3_orders_2 @ X14)
% 0.21/0.53          | (v2_struct_0 @ X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [d16_orders_2])).
% 0.21/0.53  thf('62', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X14)
% 0.21/0.53          | ~ (v3_orders_2 @ X14)
% 0.21/0.53          | ~ (v4_orders_2 @ X14)
% 0.21/0.53          | ~ (v5_orders_2 @ X14)
% 0.21/0.53          | ~ (l1_orders_2 @ X14)
% 0.21/0.53          | ~ (v6_orders_2 @ k1_xboole_0 @ X14)
% 0.21/0.53          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.53          | ~ (m2_orders_2 @ k1_xboole_0 @ X14 @ X13)
% 0.21/0.53          | ~ (m1_orders_1 @ X13 @ (k1_orders_1 @ (u1_struct_0 @ X14))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['61'])).
% 0.21/0.53  thf('63', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.21/0.53          | ~ (v6_orders_2 @ k1_xboole_0 @ sk_A)
% 0.21/0.53          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['60', '62'])).
% 0.21/0.53  thf('64', plain,
% 0.21/0.53      ((m2_orders_2 @ (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) @ sk_A @ sk_B_1)),
% 0.21/0.53      inference('clc', [status(thm)], ['13', '23'])).
% 0.21/0.53  thf('65', plain,
% 0.21/0.53      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('66', plain,
% 0.21/0.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.53         (~ (l1_orders_2 @ X23)
% 0.21/0.53          | ~ (v5_orders_2 @ X23)
% 0.21/0.53          | ~ (v4_orders_2 @ X23)
% 0.21/0.53          | ~ (v3_orders_2 @ X23)
% 0.21/0.53          | (v2_struct_0 @ X23)
% 0.21/0.53          | ~ (m1_orders_1 @ X24 @ (k1_orders_1 @ (u1_struct_0 @ X23)))
% 0.21/0.53          | (v6_orders_2 @ X25 @ X23)
% 0.21/0.53          | ~ (m2_orders_2 @ X25 @ X23 @ X24))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.53          | (v6_orders_2 @ X0 @ sk_A)
% 0.21/0.53          | (v2_struct_0 @ sk_A)
% 0.21/0.53          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.53          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.53          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.53  thf('68', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('69', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('70', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('71', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('72', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.53          | (v6_orders_2 @ X0 @ sk_A)
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['67', '68', '69', '70', '71'])).
% 0.21/0.53  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('74', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v6_orders_2 @ X0 @ sk_A) | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.21/0.53      inference('clc', [status(thm)], ['72', '73'])).
% 0.21/0.53  thf('75', plain,
% 0.21/0.53      ((v6_orders_2 @ (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['64', '74'])).
% 0.21/0.53  thf('76', plain, (((sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['55', '58'])).
% 0.21/0.53  thf('77', plain, ((v6_orders_2 @ k1_xboole_0 @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['75', '76'])).
% 0.21/0.53  thf('78', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('79', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('80', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('81', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('82', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.53          | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.21/0.53          | (v2_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['63', '77', '78', '79', '80', '81'])).
% 0.21/0.53  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('84', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.21/0.53          | ~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.53      inference('clc', [status(thm)], ['82', '83'])).
% 0.21/0.53  thf('85', plain, (~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '84'])).
% 0.21/0.53  thf('86', plain,
% 0.21/0.53      ((m2_orders_2 @ (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) @ sk_A @ sk_B_1)),
% 0.21/0.53      inference('clc', [status(thm)], ['13', '23'])).
% 0.21/0.53  thf('87', plain, (((sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['55', '58'])).
% 0.21/0.53  thf('88', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)),
% 0.21/0.53      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.53  thf('89', plain, ($false), inference('demod', [status(thm)], ['85', '88'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
