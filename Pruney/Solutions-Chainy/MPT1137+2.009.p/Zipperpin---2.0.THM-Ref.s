%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IDpO0zwmYE

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 200 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :   19
%              Number of atoms          :  584 (2534 expanded)
%              Number of equality atoms :   12 (  77 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r4_relat_2_type,type,(
    r4_relat_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X4 @ X3 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d6_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v5_orders_2 @ A )
      <=> ( r4_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ~ ( v5_orders_2 @ X14 )
      | ( r4_relat_2 @ ( u1_orders_2 @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d6_orders_2])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X18: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
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

thf('14',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( r1_orders_2 @ X16 @ X15 @ X17 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ ( u1_orders_2 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

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

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r4_relat_2 @ X10 @ X11 )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X12 ) @ X10 )
      | ( X12 = X13 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( sk_C_1 = sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( r1_orders_2 @ X16 @ X15 @ X17 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ ( u1_orders_2 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( sk_C_1 = sk_B )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','31'])).

thf('33',plain,(
    sk_B != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','34'])).

thf('36',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','37'])).

thf('39',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['42','45'])).

thf('47',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['2','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X4 @ X3 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('50',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['42','45'])).

thf('52',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['50','51'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    sk_B = sk_C_1 ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    sk_B != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IDpO0zwmYE
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:38:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 100 iterations in 0.085s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.53  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.53  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.22/0.53  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.53  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.22/0.53  thf(r4_relat_2_type, type, r4_relat_2: $i > $i > $o).
% 0.22/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.53  thf(t25_orders_2, conjecture,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.53           ( ![C:$i]:
% 0.22/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.53               ( ( ( r1_orders_2 @ A @ B @ C ) & ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.22/0.53                 ( ( B ) = ( C ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i]:
% 0.22/0.53        ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.53          ( ![B:$i]:
% 0.22/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.53              ( ![C:$i]:
% 0.22/0.53                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.53                  ( ( ( r1_orders_2 @ A @ B @ C ) & ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.22/0.53                    ( ( B ) = ( C ) ) ) ) ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t25_orders_2])).
% 0.22/0.53  thf('0', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(d2_subset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( v1_xboole_0 @ A ) =>
% 0.22/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.22/0.53       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      (![X3 : $i, X4 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X4 @ X3) | (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X3))),
% 0.22/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_C_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.53  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (![X2 : $i, X3 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X2 @ X3)
% 0.22/0.53          | (r2_hidden @ X2 @ X3)
% 0.22/0.53          | (v1_xboole_0 @ X3))),
% 0.22/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.53        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.53  thf(d6_orders_2, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( l1_orders_2 @ A ) =>
% 0.22/0.53       ( ( v5_orders_2 @ A ) <=>
% 0.22/0.53         ( r4_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      (![X14 : $i]:
% 0.22/0.53         (~ (v5_orders_2 @ X14)
% 0.22/0.53          | (r4_relat_2 @ (u1_orders_2 @ X14) @ (u1_struct_0 @ X14))
% 0.22/0.53          | ~ (l1_orders_2 @ X14))),
% 0.22/0.53      inference('cnf', [status(esa)], [d6_orders_2])).
% 0.22/0.53  thf(dt_u1_orders_2, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( l1_orders_2 @ A ) =>
% 0.22/0.53       ( m1_subset_1 @
% 0.22/0.53         ( u1_orders_2 @ A ) @ 
% 0.22/0.53         ( k1_zfmisc_1 @
% 0.22/0.53           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (![X18 : $i]:
% 0.22/0.53         ((m1_subset_1 @ (u1_orders_2 @ X18) @ 
% 0.22/0.53           (k1_zfmisc_1 @ 
% 0.22/0.53            (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X18))))
% 0.22/0.53          | ~ (l1_orders_2 @ X18))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.22/0.53  thf(cc2_relat_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ A ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (![X5 : $i, X6 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.22/0.53          | (v1_relat_1 @ X5)
% 0.22/0.53          | ~ (v1_relat_1 @ X6))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (l1_orders_2 @ X0)
% 0.22/0.53          | ~ (v1_relat_1 @ 
% 0.22/0.53               (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 0.22/0.53          | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.53  thf(fc6_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.22/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.22/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.53  thf('12', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('13', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(d9_orders_2, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( l1_orders_2 @ A ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.53           ( ![C:$i]:
% 0.22/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.53               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.22/0.53                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.22/0.53          | ~ (r1_orders_2 @ X16 @ X15 @ X17)
% 0.22/0.53          | (r2_hidden @ (k4_tarski @ X15 @ X17) @ (u1_orders_2 @ X16))
% 0.22/0.53          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.22/0.53          | ~ (l1_orders_2 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (l1_orders_2 @ sk_A)
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.53          | (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.22/0.53          | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.53  thf('16', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.53          | (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.22/0.53          | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      ((~ (r1_orders_2 @ sk_A @ sk_C_1 @ sk_B)
% 0.22/0.53        | (r2_hidden @ (k4_tarski @ sk_C_1 @ sk_B) @ (u1_orders_2 @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['12', '17'])).
% 0.22/0.53  thf('19', plain, ((r1_orders_2 @ sk_A @ sk_C_1 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      ((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_B) @ (u1_orders_2 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.53  thf(d4_relat_2, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ A ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( r4_relat_2 @ A @ B ) <=>
% 0.22/0.53           ( ![C:$i,D:$i]:
% 0.22/0.53             ( ( ( r2_hidden @ C @ B ) & ( r2_hidden @ D @ B ) & 
% 0.22/0.53                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) & 
% 0.22/0.53                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) =>
% 0.22/0.53               ( ( C ) = ( D ) ) ) ) ) ) ))).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.53         (~ (r4_relat_2 @ X10 @ X11)
% 0.22/0.53          | ~ (r2_hidden @ X12 @ X11)
% 0.22/0.53          | ~ (r2_hidden @ X13 @ X11)
% 0.22/0.53          | ~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ X10)
% 0.22/0.53          | ~ (r2_hidden @ (k4_tarski @ X13 @ X12) @ X10)
% 0.22/0.53          | ((X12) = (X13))
% 0.22/0.53          | ~ (v1_relat_1 @ X10))),
% 0.22/0.53      inference('cnf', [status(esa)], [d4_relat_2])).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.22/0.53          | ((sk_C_1) = (sk_B))
% 0.22/0.53          | ~ (r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A))
% 0.22/0.53          | ~ (r2_hidden @ sk_B @ X0)
% 0.22/0.53          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.22/0.53          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.53  thf('23', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('24', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.22/0.53          | ~ (r1_orders_2 @ X16 @ X15 @ X17)
% 0.22/0.53          | (r2_hidden @ (k4_tarski @ X15 @ X17) @ (u1_orders_2 @ X16))
% 0.22/0.53          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.22/0.53          | ~ (l1_orders_2 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (l1_orders_2 @ sk_A)
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.53          | (r2_hidden @ (k4_tarski @ sk_B @ X0) @ (u1_orders_2 @ sk_A))
% 0.22/0.53          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.53  thf('27', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('28', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.53          | (r2_hidden @ (k4_tarski @ sk_B @ X0) @ (u1_orders_2 @ sk_A))
% 0.22/0.53          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.53  thf('29', plain,
% 0.22/0.53      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 0.22/0.53        | (r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['23', '28'])).
% 0.22/0.53  thf('30', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_C_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      ((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.22/0.53          | ((sk_C_1) = (sk_B))
% 0.22/0.53          | ~ (r2_hidden @ sk_B @ X0)
% 0.22/0.53          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.22/0.53          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['22', '31'])).
% 0.22/0.53  thf('33', plain, (((sk_B) != (sk_C_1))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('34', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.22/0.53          | ~ (r2_hidden @ sk_B @ X0)
% 0.22/0.53          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.22/0.53          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0))),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.22/0.53  thf('35', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (l1_orders_2 @ sk_A)
% 0.22/0.53          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0)
% 0.22/0.53          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.22/0.53          | ~ (r2_hidden @ sk_B @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['11', '34'])).
% 0.22/0.53  thf('36', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('37', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0)
% 0.22/0.53          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.22/0.53          | ~ (r2_hidden @ sk_B @ X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.53  thf('38', plain,
% 0.22/0.53      ((~ (l1_orders_2 @ sk_A)
% 0.22/0.53        | ~ (v5_orders_2 @ sk_A)
% 0.22/0.53        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.53        | ~ (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['6', '37'])).
% 0.22/0.53  thf('39', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('40', plain, ((v5_orders_2 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('41', plain,
% 0.22/0.53      ((~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.53        | ~ (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.22/0.53  thf('42', plain,
% 0.22/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.53        | ~ (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['5', '41'])).
% 0.22/0.53  thf('43', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('44', plain,
% 0.22/0.53      (![X2 : $i, X3 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X2 @ X3)
% 0.22/0.53          | (r2_hidden @ X2 @ X3)
% 0.22/0.53          | (v1_xboole_0 @ X3))),
% 0.22/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.53  thf('45', plain,
% 0.22/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.53        | (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.53  thf('46', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.53      inference('clc', [status(thm)], ['42', '45'])).
% 0.22/0.53  thf('47', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.22/0.53      inference('demod', [status(thm)], ['2', '46'])).
% 0.22/0.53  thf('48', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('49', plain,
% 0.22/0.53      (![X3 : $i, X4 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X4 @ X3) | (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X3))),
% 0.22/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.53  thf('50', plain,
% 0.22/0.53      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.53  thf('51', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.53      inference('clc', [status(thm)], ['42', '45'])).
% 0.22/0.53  thf('52', plain, ((v1_xboole_0 @ sk_B)),
% 0.22/0.53      inference('demod', [status(thm)], ['50', '51'])).
% 0.22/0.53  thf(t8_boole, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.22/0.53  thf('53', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t8_boole])).
% 0.22/0.53  thf('54', plain, (![X0 : $i]: (((sk_B) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.53  thf('55', plain, (((sk_B) = (sk_C_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['47', '54'])).
% 0.22/0.53  thf('56', plain, (((sk_B) != (sk_C_1))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('57', plain, ($false),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['55', '56'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
