%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.quotfp8nRu

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:37 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 119 expanded)
%              Number of leaves         :   29 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  475 (1018 expanded)
%              Number of equality atoms :   48 ( 103 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('2',plain,(
    ! [X89: $i,X90: $i,X91: $i,X92: $i] :
      ( ~ ( r2_hidden @ X89 @ X90 )
      | ( X91 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X92 )
      | ~ ( v1_funct_2 @ X92 @ X90 @ X91 )
      | ~ ( m1_subset_1 @ X92 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X90 @ X91 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X92 @ X89 ) @ X91 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ sk_D_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k1_tarski @ sk_B_1 ) )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ( X15 = X14 )
      | ( X15 = X11 )
      | ( X13
       != ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('10',plain,(
    ! [X11: $i,X14: $i,X15: $i] :
      ( ( X15 = X11 )
      | ( X15 = X14 )
      | ~ ( r2_hidden @ X15 @ ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k1_tarski @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X11 )
      | ( r2_hidden @ X12 @ X13 )
      | ( X13
       != ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('18',plain,(
    ! [X11: $i,X14: $i] :
      ( r2_hidden @ X11 @ ( k2_tarski @ X14 @ X11 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('24',plain,(
    ! [X81: $i,X82: $i,X84: $i] :
      ( ( X82 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X81 @ X82 @ X84 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('25',plain,(
    ! [X81: $i,X84: $i] :
      ( ( k3_zfmisc_1 @ X81 @ k1_xboole_0 @ X84 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t54_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D )
      = ( k4_zfmisc_1 @ A @ B @ C @ D ) ) )).

thf('26',plain,(
    ! [X85: $i,X86: $i,X87: $i,X88: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X85 @ X86 ) @ X87 @ X88 )
      = ( k4_zfmisc_1 @ X85 @ X86 @ X87 @ X88 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('28',plain,(
    ! [X71: $i,X72: $i,X73: $i,X74: $i] :
      ( ( k4_zfmisc_1 @ X71 @ X72 @ X73 @ X74 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X71 @ X72 @ X73 ) @ X74 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('29',plain,(
    ! [X75: $i,X76: $i,X77: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X75 ) @ X77 )
      | ~ ( r2_hidden @ X75 @ ( k2_zfmisc_1 @ X76 @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X4 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k2_mcart_1 @ ( sk_B @ k1_xboole_0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k2_mcart_1 @ ( sk_B @ k1_xboole_0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_1 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['22','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.quotfp8nRu
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.78/0.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.78/0.95  % Solved by: fo/fo7.sh
% 0.78/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/0.95  % done 670 iterations in 0.505s
% 0.78/0.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.78/0.95  % SZS output start Refutation
% 0.78/0.95  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.78/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.78/0.95  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.78/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.78/0.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.78/0.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.78/0.95  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.78/0.95  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.78/0.95  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.78/0.95  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.78/0.95  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.78/0.95  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.78/0.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.78/0.95  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.78/0.95  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.78/0.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.78/0.95  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.78/0.95  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.78/0.95  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.78/0.95  thf(sk_B_type, type, sk_B: $i > $i).
% 0.78/0.95  thf(t65_funct_2, conjecture,
% 0.78/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.78/0.95     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.78/0.95         ( m1_subset_1 @
% 0.78/0.95           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.78/0.95       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.78/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.78/0.95    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.78/0.95        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.78/0.95            ( m1_subset_1 @
% 0.78/0.95              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.78/0.95          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.78/0.95    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.78/0.95  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('1', plain,
% 0.78/0.95      ((m1_subset_1 @ sk_D_2 @ 
% 0.78/0.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf(t7_funct_2, axiom,
% 0.78/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.78/0.95     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.78/0.95         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.78/0.95       ( ( r2_hidden @ C @ A ) =>
% 0.78/0.95         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.78/0.95           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.78/0.95  thf('2', plain,
% 0.78/0.95      (![X89 : $i, X90 : $i, X91 : $i, X92 : $i]:
% 0.78/0.95         (~ (r2_hidden @ X89 @ X90)
% 0.78/0.95          | ((X91) = (k1_xboole_0))
% 0.78/0.95          | ~ (v1_funct_1 @ X92)
% 0.78/0.95          | ~ (v1_funct_2 @ X92 @ X90 @ X91)
% 0.78/0.95          | ~ (m1_subset_1 @ X92 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X90 @ X91)))
% 0.78/0.95          | (r2_hidden @ (k1_funct_1 @ X92 @ X89) @ X91))),
% 0.78/0.95      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.78/0.95  thf('3', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k1_tarski @ sk_B_1))
% 0.78/0.95          | ~ (v1_funct_2 @ sk_D_2 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.78/0.95          | ~ (v1_funct_1 @ sk_D_2)
% 0.78/0.95          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.78/0.95          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.78/0.95      inference('sup-', [status(thm)], ['1', '2'])).
% 0.78/0.95  thf('4', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('5', plain, ((v1_funct_1 @ sk_D_2)),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('6', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k1_tarski @ sk_B_1))
% 0.78/0.95          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.78/0.95          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.78/0.95      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.78/0.95  thf('7', plain,
% 0.78/0.95      ((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.78/0.95        | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_1) @ (k1_tarski @ sk_B_1)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['0', '6'])).
% 0.78/0.95  thf(t69_enumset1, axiom,
% 0.78/0.95    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.78/0.95  thf('8', plain, (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.78/0.95      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.78/0.95  thf(d2_tarski, axiom,
% 0.78/0.95    (![A:$i,B:$i,C:$i]:
% 0.78/0.95     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.78/0.95       ( ![D:$i]:
% 0.78/0.95         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.78/0.95  thf('9', plain,
% 0.78/0.95      (![X11 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.78/0.95         (~ (r2_hidden @ X15 @ X13)
% 0.78/0.95          | ((X15) = (X14))
% 0.78/0.95          | ((X15) = (X11))
% 0.78/0.95          | ((X13) != (k2_tarski @ X14 @ X11)))),
% 0.78/0.95      inference('cnf', [status(esa)], [d2_tarski])).
% 0.78/0.95  thf('10', plain,
% 0.78/0.95      (![X11 : $i, X14 : $i, X15 : $i]:
% 0.78/0.95         (((X15) = (X11))
% 0.78/0.95          | ((X15) = (X14))
% 0.78/0.95          | ~ (r2_hidden @ X15 @ (k2_tarski @ X14 @ X11)))),
% 0.78/0.95      inference('simplify', [status(thm)], ['9'])).
% 0.78/0.95  thf('11', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i]:
% 0.78/0.95         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['8', '10'])).
% 0.78/0.95  thf('12', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i]:
% 0.78/0.95         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.78/0.95      inference('simplify', [status(thm)], ['11'])).
% 0.78/0.95  thf('13', plain,
% 0.78/0.95      ((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.78/0.95        | ((k1_funct_1 @ sk_D_2 @ sk_C_1) = (sk_B_1)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['7', '12'])).
% 0.78/0.95  thf('14', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_1) != (sk_B_1))),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('15', plain, (((k1_tarski @ sk_B_1) = (k1_xboole_0))),
% 0.78/0.95      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.78/0.95  thf('16', plain,
% 0.78/0.95      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.78/0.95      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.78/0.95  thf('17', plain,
% 0.78/0.95      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.78/0.95         (((X12) != (X11))
% 0.78/0.95          | (r2_hidden @ X12 @ X13)
% 0.78/0.95          | ((X13) != (k2_tarski @ X14 @ X11)))),
% 0.78/0.95      inference('cnf', [status(esa)], [d2_tarski])).
% 0.78/0.95  thf('18', plain,
% 0.78/0.95      (![X11 : $i, X14 : $i]: (r2_hidden @ X11 @ (k2_tarski @ X14 @ X11))),
% 0.78/0.95      inference('simplify', [status(thm)], ['17'])).
% 0.78/0.95  thf(d1_xboole_0, axiom,
% 0.78/0.95    (![A:$i]:
% 0.78/0.95     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.78/0.95  thf('19', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.78/0.95      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.78/0.95  thf('20', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.78/0.95      inference('sup-', [status(thm)], ['18', '19'])).
% 0.78/0.95  thf('21', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.78/0.95      inference('sup-', [status(thm)], ['16', '20'])).
% 0.78/0.95  thf('22', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.78/0.95      inference('sup-', [status(thm)], ['15', '21'])).
% 0.78/0.95  thf('23', plain,
% 0.78/0.95      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.78/0.95      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.78/0.95  thf(t35_mcart_1, axiom,
% 0.78/0.95    (![A:$i,B:$i,C:$i]:
% 0.78/0.95     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.78/0.95         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.78/0.95       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.78/0.95  thf('24', plain,
% 0.78/0.95      (![X81 : $i, X82 : $i, X84 : $i]:
% 0.78/0.95         (((X82) != (k1_xboole_0))
% 0.78/0.95          | ((k3_zfmisc_1 @ X81 @ X82 @ X84) = (k1_xboole_0)))),
% 0.78/0.95      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.78/0.95  thf('25', plain,
% 0.78/0.95      (![X81 : $i, X84 : $i]:
% 0.78/0.95         ((k3_zfmisc_1 @ X81 @ k1_xboole_0 @ X84) = (k1_xboole_0))),
% 0.78/0.95      inference('simplify', [status(thm)], ['24'])).
% 0.78/0.95  thf(t54_mcart_1, axiom,
% 0.78/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.78/0.95     ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D ) =
% 0.78/0.95       ( k4_zfmisc_1 @ A @ B @ C @ D ) ))).
% 0.78/0.95  thf('26', plain,
% 0.78/0.95      (![X85 : $i, X86 : $i, X87 : $i, X88 : $i]:
% 0.78/0.95         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X85 @ X86) @ X87 @ X88)
% 0.78/0.95           = (k4_zfmisc_1 @ X85 @ X86 @ X87 @ X88))),
% 0.78/0.95      inference('cnf', [status(esa)], [t54_mcart_1])).
% 0.78/0.95  thf('27', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.95         ((k1_xboole_0) = (k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0))),
% 0.78/0.95      inference('sup+', [status(thm)], ['25', '26'])).
% 0.78/0.95  thf(d4_zfmisc_1, axiom,
% 0.78/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.78/0.95     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.78/0.95       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.78/0.95  thf('28', plain,
% 0.78/0.95      (![X71 : $i, X72 : $i, X73 : $i, X74 : $i]:
% 0.78/0.95         ((k4_zfmisc_1 @ X71 @ X72 @ X73 @ X74)
% 0.78/0.95           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X71 @ X72 @ X73) @ X74))),
% 0.78/0.95      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.78/0.95  thf(t10_mcart_1, axiom,
% 0.78/0.95    (![A:$i,B:$i,C:$i]:
% 0.78/0.95     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.78/0.95       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.78/0.95         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.78/0.95  thf('29', plain,
% 0.78/0.95      (![X75 : $i, X76 : $i, X77 : $i]:
% 0.78/0.95         ((r2_hidden @ (k2_mcart_1 @ X75) @ X77)
% 0.78/0.95          | ~ (r2_hidden @ X75 @ (k2_zfmisc_1 @ X76 @ X77)))),
% 0.78/0.95      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.78/0.95  thf('30', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.78/0.95         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.78/0.95          | (r2_hidden @ (k2_mcart_1 @ X4) @ X0))),
% 0.78/0.95      inference('sup-', [status(thm)], ['28', '29'])).
% 0.78/0.95  thf('31', plain,
% 0.78/0.95      (![X0 : $i, X3 : $i]:
% 0.78/0.95         (~ (r2_hidden @ X3 @ k1_xboole_0)
% 0.78/0.95          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.78/0.95      inference('sup-', [status(thm)], ['27', '30'])).
% 0.78/0.95  thf('32', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         ((v1_xboole_0 @ k1_xboole_0)
% 0.78/0.95          | (r2_hidden @ (k2_mcart_1 @ (sk_B @ k1_xboole_0)) @ X0))),
% 0.78/0.95      inference('sup-', [status(thm)], ['23', '31'])).
% 0.78/0.95  thf('33', plain,
% 0.78/0.95      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.78/0.95      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.78/0.95  thf('34', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i]:
% 0.78/0.95         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.78/0.95      inference('simplify', [status(thm)], ['11'])).
% 0.78/0.95  thf('35', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i]:
% 0.78/0.95         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0)) | ((X1) = (X0)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['33', '34'])).
% 0.78/0.95  thf('36', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         ((v1_xboole_0 @ k1_xboole_0)
% 0.78/0.95          | ((k2_mcart_1 @ (sk_B @ k1_xboole_0)) = (X0)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['32', '35'])).
% 0.78/0.95  thf('37', plain,
% 0.78/0.95      (![X0 : $i]:
% 0.78/0.95         ((v1_xboole_0 @ k1_xboole_0)
% 0.78/0.95          | ((k2_mcart_1 @ (sk_B @ k1_xboole_0)) = (X0)))),
% 0.78/0.95      inference('sup-', [status(thm)], ['32', '35'])).
% 0.78/0.95  thf('38', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i]:
% 0.78/0.95         (((X0) = (X1))
% 0.78/0.95          | (v1_xboole_0 @ k1_xboole_0)
% 0.78/0.95          | (v1_xboole_0 @ k1_xboole_0))),
% 0.78/0.95      inference('sup+', [status(thm)], ['36', '37'])).
% 0.78/0.95  thf('39', plain,
% 0.78/0.95      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ k1_xboole_0) | ((X0) = (X1)))),
% 0.78/0.95      inference('simplify', [status(thm)], ['38'])).
% 0.78/0.95  thf('40', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_1) != (sk_B_1))),
% 0.78/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.95  thf('41', plain,
% 0.78/0.95      (![X0 : $i]: (((X0) != (sk_B_1)) | (v1_xboole_0 @ k1_xboole_0))),
% 0.78/0.95      inference('sup-', [status(thm)], ['39', '40'])).
% 0.78/0.95  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.78/0.95      inference('simplify', [status(thm)], ['41'])).
% 0.78/0.95  thf('43', plain, ($false), inference('demod', [status(thm)], ['22', '42'])).
% 0.78/0.95  
% 0.78/0.95  % SZS output end Refutation
% 0.78/0.95  
% 0.78/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
