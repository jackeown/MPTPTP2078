%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jl3bItKDZv

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:34 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 129 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :   19
%              Number of atoms          :  578 (1551 expanded)
%              Number of equality atoms :    7 (  43 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r4_relat_2_type,type,(
    r4_relat_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t25_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_orders_2 @ A @ B @ C )
                  & ( r1_orders_2 @ A @ C @ B ) )
               => ( B = C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( ( r1_orders_2 @ A @ B @ C )
                    & ( r1_orders_2 @ A @ C @ B ) )
                 => ( B = C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_orders_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r1_orders_2 @ X18 @ X17 @ X19 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ ( u1_orders_2 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d6_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v5_orders_2 @ A )
      <=> ( r4_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X16: $i] :
      ( ~ ( v5_orders_2 @ X16 )
      | ( r4_relat_2 @ ( u1_orders_2 @ X16 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d6_orders_2])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d4_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r4_relat_2 @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ B )
                & ( r2_hidden @ D @ B )
                & ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
                & ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) )
             => ( C = D ) ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r4_relat_2 @ X12 @ X13 )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X14 ) @ X12 )
      | ( X14 = X15 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( sk_B = sk_C_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r1_orders_2 @ X18 @ X17 @ X19 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ ( u1_orders_2 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( sk_B = sk_C_1 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['23','32'])).

thf('34',plain,(
    sk_B != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','35'])).

thf('37',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('45',plain,(
    ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','45'])).

thf('47',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('48',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X8 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( u1_orders_2 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_xboole_0 @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['10','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jl3bItKDZv
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:08:31 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 82 iterations in 0.047s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.50  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.19/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.50  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.19/0.50  thf(r4_relat_2_type, type, r4_relat_2: $i > $i > $o).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.50  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.19/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.50  thf(t25_orders_2, conjecture,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.50               ( ( ( r1_orders_2 @ A @ B @ C ) & ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.19/0.50                 ( ( B ) = ( C ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i]:
% 0.19/0.50        ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.50          ( ![B:$i]:
% 0.19/0.50            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.50              ( ![C:$i]:
% 0.19/0.50                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.50                  ( ( ( r1_orders_2 @ A @ B @ C ) & ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.19/0.50                    ( ( B ) = ( C ) ) ) ) ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t25_orders_2])).
% 0.19/0.50  thf('0', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(d9_orders_2, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( l1_orders_2 @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.50               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.19/0.50                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.19/0.50          | ~ (r1_orders_2 @ X18 @ X17 @ X19)
% 0.19/0.50          | (r2_hidden @ (k4_tarski @ X17 @ X19) @ (u1_orders_2 @ X18))
% 0.19/0.50          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.19/0.50          | ~ (l1_orders_2 @ X18))),
% 0.19/0.50      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (l1_orders_2 @ sk_A)
% 0.19/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50          | (r2_hidden @ (k4_tarski @ sk_B @ X0) @ (u1_orders_2 @ sk_A))
% 0.19/0.50          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.50  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50          | (r2_hidden @ (k4_tarski @ sk_B @ X0) @ (u1_orders_2 @ sk_A))
% 0.19/0.50          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.19/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 0.19/0.50        | (r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['0', '5'])).
% 0.19/0.50  thf('7', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_C_1)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      ((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.50  thf(t7_boole, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [t7_boole])).
% 0.19/0.50  thf('10', plain, (~ (v1_xboole_0 @ (u1_orders_2 @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.50  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(d2_subset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( v1_xboole_0 @ A ) =>
% 0.19/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.19/0.50       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X2 : $i, X3 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X2 @ X3)
% 0.19/0.50          | (r2_hidden @ X2 @ X3)
% 0.19/0.50          | (v1_xboole_0 @ X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.50  thf('14', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (![X2 : $i, X3 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X2 @ X3)
% 0.19/0.50          | (r2_hidden @ X2 @ X3)
% 0.19/0.50          | (v1_xboole_0 @ X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.50  thf(d6_orders_2, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( l1_orders_2 @ A ) =>
% 0.19/0.50       ( ( v5_orders_2 @ A ) <=>
% 0.19/0.50         ( r4_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X16 : $i]:
% 0.19/0.50         (~ (v5_orders_2 @ X16)
% 0.19/0.50          | (r4_relat_2 @ (u1_orders_2 @ X16) @ (u1_struct_0 @ X16))
% 0.19/0.50          | ~ (l1_orders_2 @ X16))),
% 0.19/0.50      inference('cnf', [status(esa)], [d6_orders_2])).
% 0.19/0.50  thf(dt_u1_orders_2, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( l1_orders_2 @ A ) =>
% 0.19/0.50       ( m1_subset_1 @
% 0.19/0.50         ( u1_orders_2 @ A ) @ 
% 0.19/0.50         ( k1_zfmisc_1 @
% 0.19/0.50           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      (![X20 : $i]:
% 0.19/0.50         ((m1_subset_1 @ (u1_orders_2 @ X20) @ 
% 0.19/0.50           (k1_zfmisc_1 @ 
% 0.19/0.50            (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X20))))
% 0.19/0.50          | ~ (l1_orders_2 @ X20))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.19/0.50  thf(cc1_relset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.50       ( v1_relat_1 @ C ) ))).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.50         ((v1_relat_1 @ X5)
% 0.19/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.19/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      ((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.50  thf(d4_relat_2, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( r4_relat_2 @ A @ B ) <=>
% 0.19/0.50           ( ![C:$i,D:$i]:
% 0.19/0.50             ( ( ( r2_hidden @ C @ B ) & ( r2_hidden @ D @ B ) & 
% 0.19/0.50                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) & 
% 0.19/0.50                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) =>
% 0.19/0.50               ( ( C ) = ( D ) ) ) ) ) ) ))).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.50         (~ (r4_relat_2 @ X12 @ X13)
% 0.19/0.50          | ~ (r2_hidden @ X14 @ X13)
% 0.19/0.50          | ~ (r2_hidden @ X15 @ X13)
% 0.19/0.50          | ~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X12)
% 0.19/0.50          | ~ (r2_hidden @ (k4_tarski @ X15 @ X14) @ X12)
% 0.19/0.50          | ((X14) = (X15))
% 0.19/0.50          | ~ (v1_relat_1 @ X12))),
% 0.19/0.50      inference('cnf', [status(esa)], [d4_relat_2])).
% 0.19/0.50  thf('23', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.19/0.50          | ((sk_B) = (sk_C_1))
% 0.19/0.50          | ~ (r2_hidden @ (k4_tarski @ sk_C_1 @ sk_B) @ (u1_orders_2 @ sk_A))
% 0.19/0.50          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.19/0.50          | ~ (r2_hidden @ sk_B @ X0)
% 0.19/0.50          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.50  thf('24', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('25', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.19/0.50          | ~ (r1_orders_2 @ X18 @ X17 @ X19)
% 0.19/0.50          | (r2_hidden @ (k4_tarski @ X17 @ X19) @ (u1_orders_2 @ X18))
% 0.19/0.50          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.19/0.50          | ~ (l1_orders_2 @ X18))),
% 0.19/0.50      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (l1_orders_2 @ sk_A)
% 0.19/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50          | (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.19/0.50          | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.50  thf('28', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50          | (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.19/0.50          | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ X0))),
% 0.19/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.50  thf('30', plain,
% 0.19/0.50      ((~ (r1_orders_2 @ sk_A @ sk_C_1 @ sk_B)
% 0.19/0.50        | (r2_hidden @ (k4_tarski @ sk_C_1 @ sk_B) @ (u1_orders_2 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['24', '29'])).
% 0.19/0.50  thf('31', plain, ((r1_orders_2 @ sk_A @ sk_C_1 @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('32', plain,
% 0.19/0.50      ((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_B) @ (u1_orders_2 @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.19/0.50  thf('33', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.19/0.50          | ((sk_B) = (sk_C_1))
% 0.19/0.50          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.19/0.50          | ~ (r2_hidden @ sk_B @ X0)
% 0.19/0.50          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0))),
% 0.19/0.50      inference('demod', [status(thm)], ['23', '32'])).
% 0.19/0.50  thf('34', plain, (((sk_B) != (sk_C_1))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('35', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.19/0.50          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.19/0.50          | ~ (r2_hidden @ sk_B @ X0)
% 0.19/0.50          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (l1_orders_2 @ sk_A)
% 0.19/0.50          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0)
% 0.19/0.50          | ~ (r2_hidden @ sk_B @ X0)
% 0.19/0.50          | ~ (r2_hidden @ sk_C_1 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['20', '35'])).
% 0.19/0.50  thf('37', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('38', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0)
% 0.19/0.50          | ~ (r2_hidden @ sk_B @ X0)
% 0.19/0.50          | ~ (r2_hidden @ sk_C_1 @ X0))),
% 0.19/0.50      inference('demod', [status(thm)], ['36', '37'])).
% 0.19/0.50  thf('39', plain,
% 0.19/0.50      ((~ (l1_orders_2 @ sk_A)
% 0.19/0.50        | ~ (v5_orders_2 @ sk_A)
% 0.19/0.50        | ~ (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['17', '38'])).
% 0.19/0.50  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('42', plain,
% 0.19/0.50      ((~ (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.19/0.50  thf('43', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['16', '42'])).
% 0.19/0.50  thf('44', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [t7_boole])).
% 0.19/0.50  thf('45', plain, (~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('clc', [status(thm)], ['43', '44'])).
% 0.19/0.50  thf('46', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['13', '45'])).
% 0.19/0.50  thf('47', plain,
% 0.19/0.50      (![X20 : $i]:
% 0.19/0.50         ((m1_subset_1 @ (u1_orders_2 @ X20) @ 
% 0.19/0.50           (k1_zfmisc_1 @ 
% 0.19/0.50            (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X20))))
% 0.19/0.50          | ~ (l1_orders_2 @ X20))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.19/0.50  thf(cc4_relset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_xboole_0 @ A ) =>
% 0.19/0.50       ( ![C:$i]:
% 0.19/0.50         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.50           ( v1_xboole_0 @ C ) ) ) ))).
% 0.19/0.50  thf('48', plain,
% 0.19/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.50         (~ (v1_xboole_0 @ X8)
% 0.19/0.50          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X8)))
% 0.19/0.50          | (v1_xboole_0 @ X9))),
% 0.19/0.50      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.19/0.50  thf('49', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (l1_orders_2 @ X0)
% 0.19/0.50          | (v1_xboole_0 @ (u1_orders_2 @ X0))
% 0.19/0.50          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.50  thf('50', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_orders_2 @ sk_A)) | ~ (l1_orders_2 @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['46', '49'])).
% 0.19/0.50  thf('51', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('52', plain, ((v1_xboole_0 @ (u1_orders_2 @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['50', '51'])).
% 0.19/0.50  thf('53', plain, ($false), inference('demod', [status(thm)], ['10', '52'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
