%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LWG1zu0X8C

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:34 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 194 expanded)
%              Number of leaves         :   24 (  66 expanded)
%              Depth                    :   19
%              Number of atoms          :  565 (2496 expanded)
%              Number of equality atoms :   12 (  77 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r4_relat_2_type,type,(
    r4_relat_2: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ! [X13: $i] :
      ( ~ ( v5_orders_2 @ X13 )
      | ( r4_relat_2 @ ( u1_orders_2 @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_orders_2])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_orders_2 @ X15 @ X14 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( u1_orders_2 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_B ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

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

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r4_relat_2 @ X9 @ X10 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X11 ) @ X9 )
      | ( X11 = X12 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( sk_C_1 = sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_orders_2 @ X15 @ X14 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( u1_orders_2 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( sk_C_1 = sk_B )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','29'])).

thf('31',plain,(
    sk_B != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','32'])).

thf('34',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r4_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','35'])).

thf('37',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','43'])).

thf('45',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['2','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X4 @ X3 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','43'])).

thf('50',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['48','49'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    sk_B = sk_C_1 ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,(
    sk_B != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LWG1zu0X8C
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 100 iterations in 0.090s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.36/0.55  thf(r4_relat_2_type, type, r4_relat_2: $i > $i > $o).
% 0.36/0.55  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.36/0.55  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.55  thf(t25_orders_2, conjecture,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.55               ( ( ( r1_orders_2 @ A @ B @ C ) & ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.36/0.55                 ( ( B ) = ( C ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i]:
% 0.36/0.55        ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.36/0.55          ( ![B:$i]:
% 0.36/0.55            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.55              ( ![C:$i]:
% 0.36/0.55                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.55                  ( ( ( r1_orders_2 @ A @ B @ C ) & ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.36/0.55                    ( ( B ) = ( C ) ) ) ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t25_orders_2])).
% 0.36/0.55  thf('0', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(d2_subset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( v1_xboole_0 @ A ) =>
% 0.36/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.36/0.55       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      (![X3 : $i, X4 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X4 @ X3) | (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X3))),
% 0.36/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_C_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.55  thf('3', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X2 @ X3)
% 0.36/0.55          | (r2_hidden @ X2 @ X3)
% 0.36/0.55          | (v1_xboole_0 @ X3))),
% 0.36/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.55  thf(d6_orders_2, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_orders_2 @ A ) =>
% 0.36/0.55       ( ( v5_orders_2 @ A ) <=>
% 0.36/0.55         ( r4_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X13 : $i]:
% 0.36/0.55         (~ (v5_orders_2 @ X13)
% 0.36/0.55          | (r4_relat_2 @ (u1_orders_2 @ X13) @ (u1_struct_0 @ X13))
% 0.36/0.55          | ~ (l1_orders_2 @ X13))),
% 0.36/0.55      inference('cnf', [status(esa)], [d6_orders_2])).
% 0.36/0.55  thf(dt_u1_orders_2, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_orders_2 @ A ) =>
% 0.36/0.55       ( m1_subset_1 @
% 0.36/0.55         ( u1_orders_2 @ A ) @ 
% 0.36/0.55         ( k1_zfmisc_1 @
% 0.36/0.55           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X17 : $i]:
% 0.36/0.55         ((m1_subset_1 @ (u1_orders_2 @ X17) @ 
% 0.36/0.55           (k1_zfmisc_1 @ 
% 0.36/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X17))))
% 0.36/0.55          | ~ (l1_orders_2 @ X17))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.36/0.55  thf(cc1_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( v1_relat_1 @ C ) ))).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.55         ((v1_relat_1 @ X5)
% 0.36/0.55          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.55  thf('10', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('11', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(d9_orders_2, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_orders_2 @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.55               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.36/0.55                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.36/0.55          | ~ (r1_orders_2 @ X15 @ X14 @ X16)
% 0.36/0.55          | (r2_hidden @ (k4_tarski @ X14 @ X16) @ (u1_orders_2 @ X15))
% 0.36/0.55          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.36/0.55          | ~ (l1_orders_2 @ X15))),
% 0.36/0.55      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ sk_A)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.36/0.55          | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.55  thf('14', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.36/0.55          | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      ((~ (r1_orders_2 @ sk_A @ sk_C_1 @ sk_B)
% 0.36/0.55        | (r2_hidden @ (k4_tarski @ sk_C_1 @ sk_B) @ (u1_orders_2 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['10', '15'])).
% 0.36/0.55  thf('17', plain, ((r1_orders_2 @ sk_A @ sk_C_1 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      ((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_B) @ (u1_orders_2 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.36/0.55  thf(d4_relat_2, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( v1_relat_1 @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( r4_relat_2 @ A @ B ) <=>
% 0.36/0.55           ( ![C:$i,D:$i]:
% 0.36/0.55             ( ( ( r2_hidden @ C @ B ) & ( r2_hidden @ D @ B ) & 
% 0.36/0.55                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) & 
% 0.36/0.55                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) =>
% 0.36/0.55               ( ( C ) = ( D ) ) ) ) ) ) ))).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.55         (~ (r4_relat_2 @ X9 @ X10)
% 0.36/0.55          | ~ (r2_hidden @ X11 @ X10)
% 0.36/0.55          | ~ (r2_hidden @ X12 @ X10)
% 0.36/0.55          | ~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X9)
% 0.36/0.55          | ~ (r2_hidden @ (k4_tarski @ X12 @ X11) @ X9)
% 0.36/0.55          | ((X11) = (X12))
% 0.36/0.55          | ~ (v1_relat_1 @ X9))),
% 0.36/0.55      inference('cnf', [status(esa)], [d4_relat_2])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.36/0.55          | ((sk_C_1) = (sk_B))
% 0.36/0.55          | ~ (r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A))
% 0.36/0.55          | ~ (r2_hidden @ sk_B @ X0)
% 0.36/0.55          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.36/0.55          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.55  thf('21', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('22', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.36/0.55          | ~ (r1_orders_2 @ X15 @ X14 @ X16)
% 0.36/0.55          | (r2_hidden @ (k4_tarski @ X14 @ X16) @ (u1_orders_2 @ X15))
% 0.36/0.55          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.36/0.55          | ~ (l1_orders_2 @ X15))),
% 0.36/0.55      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ sk_A)
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | (r2_hidden @ (k4_tarski @ sk_B @ X0) @ (u1_orders_2 @ sk_A))
% 0.36/0.55          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.55  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | (r2_hidden @ (k4_tarski @ sk_B @ X0) @ (u1_orders_2 @ sk_A))
% 0.36/0.55          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 0.36/0.55        | (r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['21', '26'])).
% 0.36/0.55  thf('28', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_C_1)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      ((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['27', '28'])).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.36/0.55          | ((sk_C_1) = (sk_B))
% 0.36/0.55          | ~ (r2_hidden @ sk_B @ X0)
% 0.36/0.55          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.36/0.55          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['20', '29'])).
% 0.36/0.55  thf('31', plain, (((sk_B) != (sk_C_1))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.36/0.55          | ~ (r2_hidden @ sk_B @ X0)
% 0.36/0.55          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.36/0.55          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0))),
% 0.36/0.55      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_orders_2 @ sk_A)
% 0.36/0.55          | ~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0)
% 0.36/0.55          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.36/0.55          | ~ (r2_hidden @ sk_B @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['9', '32'])).
% 0.36/0.55  thf('34', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (r4_relat_2 @ (u1_orders_2 @ sk_A) @ X0)
% 0.36/0.55          | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.36/0.55          | ~ (r2_hidden @ sk_B @ X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['33', '34'])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      ((~ (l1_orders_2 @ sk_A)
% 0.36/0.55        | ~ (v5_orders_2 @ sk_A)
% 0.36/0.55        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.36/0.55        | ~ (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['6', '35'])).
% 0.36/0.55  thf('37', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('38', plain, ((v5_orders_2 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('39', plain,
% 0.36/0.55      ((~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.36/0.55        | ~ (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55        | ~ (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['5', '39'])).
% 0.36/0.55  thf('41', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('42', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X2 @ X3)
% 0.36/0.55          | (r2_hidden @ X2 @ X3)
% 0.36/0.55          | (v1_xboole_0 @ X3))),
% 0.36/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.36/0.55  thf('43', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55        | (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['41', '42'])).
% 0.36/0.55  thf('44', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('clc', [status(thm)], ['40', '43'])).
% 0.36/0.55  thf('45', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.36/0.55      inference('demod', [status(thm)], ['2', '44'])).
% 0.36/0.55  thf('46', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('47', plain,
% 0.36/0.55      (![X3 : $i, X4 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X4 @ X3) | (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X3))),
% 0.36/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.36/0.55  thf('48', plain,
% 0.36/0.55      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.36/0.55  thf('49', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('clc', [status(thm)], ['40', '43'])).
% 0.36/0.55  thf('50', plain, ((v1_xboole_0 @ sk_B)),
% 0.36/0.55      inference('demod', [status(thm)], ['48', '49'])).
% 0.36/0.55  thf(t8_boole, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.36/0.55  thf('51', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t8_boole])).
% 0.36/0.55  thf('52', plain, (![X0 : $i]: (((sk_B) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.55  thf('53', plain, (((sk_B) = (sk_C_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['45', '52'])).
% 0.36/0.55  thf('54', plain, (((sk_B) != (sk_C_1))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('55', plain, ($false),
% 0.36/0.55      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
