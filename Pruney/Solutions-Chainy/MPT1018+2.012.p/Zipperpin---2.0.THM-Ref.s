%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zn4j1YRyy2

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:57 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 407 expanded)
%              Number of leaves         :   28 ( 129 expanded)
%              Depth                    :   17
%              Number of atoms          :  546 (7108 expanded)
%              Number of equality atoms :   52 ( 536 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t85_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v2_funct_1 @ B )
       => ! [C: $i,D: $i] :
            ( ( ( r2_hidden @ C @ A )
              & ( r2_hidden @ D @ A )
              & ( ( k1_funct_1 @ B @ C )
                = ( k1_funct_1 @ B @ D ) ) )
           => ( C = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( v2_funct_1 @ B )
         => ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A )
                & ( ( k1_funct_1 @ B @ C )
                  = ( k1_funct_1 @ B @ D ) ) )
             => ( C = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t85_funct_2])).

thf('0',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v4_relat_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('10',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['5','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ D )
          & ( r2_hidden @ C @ A ) )
       => ( ( B = k1_xboole_0 )
          | ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) )
            = C ) ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( X18 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X19 ) @ ( k1_funct_1 @ X19 @ X16 ) )
        = X16 )
      | ~ ( v2_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('25',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    sk_C_1 != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('32',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('33',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('34',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','31','32','33'])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X10 ) )
      | ( ( k1_funct_1 @ X10 @ X11 )
       != ( k1_funct_1 @ X10 @ X12 ) )
      | ( X11 = X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['8','9'])).

thf('38',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','31','32','33'])).

thf('40',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( sk_D = X0 )
      | ~ ( r2_hidden @ sk_D @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','41'])).

thf('43',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('45',plain,(
    r2_hidden @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( sk_D = X0 ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,
    ( ( sk_D = sk_C_1 )
    | ~ ( r2_hidden @ sk_C_1 @ k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['46'])).

thf('48',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('50',plain,(
    r2_hidden @ sk_C_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    sk_D = sk_C_1 ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    sk_C_1 != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zn4j1YRyy2
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:48 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 48 iterations in 0.035s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.50  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.19/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.50  thf(t85_funct_2, conjecture,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.19/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.50       ( ( v2_funct_1 @ B ) =>
% 0.19/0.50         ( ![C:$i,D:$i]:
% 0.19/0.50           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.19/0.50               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.19/0.50             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i]:
% 0.19/0.50        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.19/0.50            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.50          ( ( v2_funct_1 @ B ) =>
% 0.19/0.50            ( ![C:$i,D:$i]:
% 0.19/0.50              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.19/0.50                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.19/0.50                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t85_funct_2])).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(cc2_relset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.50         ((v4_relat_1 @ X13 @ X14)
% 0.19/0.50          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.19/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.50  thf('3', plain, ((v4_relat_1 @ sk_B_1 @ sk_A)),
% 0.19/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.50  thf(d18_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ B ) =>
% 0.19/0.50       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (![X6 : $i, X7 : $i]:
% 0.19/0.50         (~ (v4_relat_1 @ X6 @ X7)
% 0.19/0.50          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.19/0.50          | ~ (v1_relat_1 @ X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      ((~ (v1_relat_1 @ sk_B_1) | (r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(cc2_relat_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (![X4 : $i, X5 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.19/0.50          | (v1_relat_1 @ X4)
% 0.19/0.50          | ~ (v1_relat_1 @ X5))),
% 0.19/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.50  thf(fc6_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.50  thf('10', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.50  thf('11', plain, ((r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.19/0.50      inference('demod', [status(thm)], ['5', '10'])).
% 0.19/0.50  thf(d10_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X0 : $i, X2 : $i]:
% 0.19/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.19/0.50        | ((sk_A) = (k1_relat_1 @ sk_B_1)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.50  thf('14', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t32_funct_2, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.19/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.50       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.19/0.50         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.50           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.19/0.50             ( C ) ) ) ) ))).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X16 @ X17)
% 0.19/0.50          | ((X18) = (k1_xboole_0))
% 0.19/0.50          | ~ (v1_funct_1 @ X19)
% 0.19/0.50          | ~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.19/0.50          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.19/0.50          | ((k1_funct_1 @ (k2_funct_1 @ X19) @ (k1_funct_1 @ X19 @ X16))
% 0.19/0.50              = (X16))
% 0.19/0.50          | ~ (v2_funct_1 @ X19))),
% 0.19/0.50      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (v2_funct_1 @ sk_B_1)
% 0.19/0.50          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.19/0.50              = (X0))
% 0.19/0.50          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.19/0.50          | ~ (v1_funct_1 @ sk_B_1)
% 0.19/0.50          | ((sk_A) = (k1_xboole_0))
% 0.19/0.50          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.50  thf('18', plain, ((v2_funct_1 @ sk_B_1)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('19', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('20', plain, ((v1_funct_1 @ sk_B_1)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.19/0.50            = (X0))
% 0.19/0.50          | ((sk_A) = (k1_xboole_0))
% 0.19/0.50          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      ((((sk_A) = (k1_xboole_0))
% 0.19/0.50        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.19/0.50            = (sk_C_1)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['14', '21'])).
% 0.19/0.50  thf('23', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.19/0.50            = (X0))
% 0.19/0.50          | ((sk_A) = (k1_xboole_0))
% 0.19/0.50          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      ((((sk_A) = (k1_xboole_0))
% 0.19/0.50        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.19/0.50            = (sk_D)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      ((((sk_A) = (k1_xboole_0))
% 0.19/0.50        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.19/0.50            = (sk_D)))),
% 0.19/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      ((((sk_C_1) = (sk_D))
% 0.19/0.50        | ((sk_A) = (k1_xboole_0))
% 0.19/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['22', '27'])).
% 0.19/0.50  thf('29', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_1) = (sk_D)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.19/0.50  thf('30', plain, (((sk_C_1) != (sk_D))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('31', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.50  thf('32', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.19/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.50  thf('33', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf('34', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_B_1))),
% 0.19/0.50      inference('demod', [status(thm)], ['13', '31', '32', '33'])).
% 0.19/0.50  thf(d8_funct_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.50       ( ( v2_funct_1 @ A ) <=>
% 0.19/0.50         ( ![B:$i,C:$i]:
% 0.19/0.50           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.19/0.50               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.19/0.50               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.19/0.50             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.19/0.50  thf('35', plain,
% 0.19/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.50         (~ (v2_funct_1 @ X10)
% 0.19/0.50          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X10))
% 0.19/0.50          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X10))
% 0.19/0.50          | ((k1_funct_1 @ X10 @ X11) != (k1_funct_1 @ X10 @ X12))
% 0.19/0.50          | ((X11) = (X12))
% 0.19/0.50          | ~ (v1_funct_1 @ X10)
% 0.19/0.50          | ~ (v1_relat_1 @ X10))),
% 0.19/0.50      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.19/0.50          | ~ (v1_relat_1 @ sk_B_1)
% 0.19/0.50          | ~ (v1_funct_1 @ sk_B_1)
% 0.19/0.50          | ((X0) = (X1))
% 0.19/0.50          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.19/0.50          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.19/0.50          | ~ (v2_funct_1 @ sk_B_1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.50  thf('37', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.50  thf('38', plain, ((v1_funct_1 @ sk_B_1)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('39', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_B_1))),
% 0.19/0.50      inference('demod', [status(thm)], ['13', '31', '32', '33'])).
% 0.19/0.50  thf('40', plain, ((v2_funct_1 @ sk_B_1)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('41', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.19/0.50          | ((X0) = (X1))
% 0.19/0.50          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.19/0.50          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.19/0.50      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 0.19/0.50  thf('42', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.19/0.50          | ~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.19/0.50          | ((sk_D) = (X0))
% 0.19/0.50          | ~ (r2_hidden @ sk_D @ k1_xboole_0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['0', '41'])).
% 0.19/0.50  thf('43', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('44', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf('45', plain, ((r2_hidden @ sk_D @ k1_xboole_0)),
% 0.19/0.50      inference('demod', [status(thm)], ['43', '44'])).
% 0.19/0.50  thf('46', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.19/0.50          | ~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.19/0.50          | ((sk_D) = (X0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['42', '45'])).
% 0.19/0.50  thf('47', plain,
% 0.19/0.50      ((((sk_D) = (sk_C_1)) | ~ (r2_hidden @ sk_C_1 @ k1_xboole_0))),
% 0.19/0.50      inference('eq_res', [status(thm)], ['46'])).
% 0.19/0.50  thf('48', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('49', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf('50', plain, ((r2_hidden @ sk_C_1 @ k1_xboole_0)),
% 0.19/0.50      inference('demod', [status(thm)], ['48', '49'])).
% 0.19/0.50  thf('51', plain, (((sk_D) = (sk_C_1))),
% 0.19/0.50      inference('demod', [status(thm)], ['47', '50'])).
% 0.19/0.50  thf('52', plain, (((sk_C_1) != (sk_D))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('53', plain, ($false),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
