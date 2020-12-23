%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H7y1xsDlxj

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:41 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   77 (  87 expanded)
%              Number of leaves         :   36 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  669 ( 876 expanded)
%              Number of equality atoms :   63 (  74 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(d4_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( ( H != F )
              & ( H != E )
              & ( H != D )
              & ( H != C )
              & ( H != B )
              & ( H != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [H: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A )
    <=> ( ( H != A )
        & ( H != B )
        & ( H != C )
        & ( H != D )
        & ( H != E )
        & ( H != F ) ) ) )).

thf('0',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 )
      | ( X38 = X39 )
      | ( X38 = X40 )
      | ( X38 = X41 )
      | ( X38 = X42 )
      | ( X38 = X43 )
      | ( X38 = X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('1',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('3',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ~ ( r2_hidden @ X58 @ X59 )
      | ( X60 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X61 )
      | ~ ( v1_funct_2 @ X61 @ X59 @ X60 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X61 @ X58 ) @ X60 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B_1 ) )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('8',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35 != X34 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X35 ) @ ( k1_tarski @ X34 ) )
       != ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('9',plain,(
    ! [X34: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X34 ) )
     != ( k1_tarski @ X34 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('10',plain,(
    ! [X55: $i] :
      ( ( X55 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X55 ) @ X55 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X55: $i] :
      ( ( X55 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X55 ) @ X55 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X34: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X34 ) ) ),
    inference(demod,[status(thm)],['9','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['7','20'])).

thf('22',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','21'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('23',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X53 @ X52 )
      | ~ ( zip_tseitin_0 @ X53 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 )
      | ( X52
       != ( k4_enumset1 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X53: $i] :
      ( ~ ( zip_tseitin_0 @ X53 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 )
      | ~ ( r2_hidden @ X53 @ ( k4_enumset1 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','33'])).

thf('35',plain,(
    ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D_1 @ sk_C ) @ sk_B_1 @ sk_B_1 @ sk_B_1 @ sk_B_1 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','34'])).

thf('36',plain,
    ( ( ( k1_funct_1 @ sk_D_1 @ sk_C )
      = sk_B_1 )
    | ( ( k1_funct_1 @ sk_D_1 @ sk_C )
      = sk_B_1 )
    | ( ( k1_funct_1 @ sk_D_1 @ sk_C )
      = sk_B_1 )
    | ( ( k1_funct_1 @ sk_D_1 @ sk_C )
      = sk_B_1 )
    | ( ( k1_funct_1 @ sk_D_1 @ sk_C )
      = sk_B_1 )
    | ( ( k1_funct_1 @ sk_D_1 @ sk_C )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','35'])).

thf('37',plain,
    ( ( k1_funct_1 @ sk_D_1 @ sk_C )
    = sk_B_1 ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ( k1_funct_1 @ sk_D_1 @ sk_C )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H7y1xsDlxj
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:54:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.84/1.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.06  % Solved by: fo/fo7.sh
% 0.84/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.06  % done 247 iterations in 0.604s
% 0.84/1.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.06  % SZS output start Refutation
% 0.84/1.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.06  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.84/1.06  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.84/1.06  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.84/1.06  thf(sk_B_type, type, sk_B: $i > $i).
% 0.84/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.06  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 0.84/1.06  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.84/1.06  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.84/1.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.84/1.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.84/1.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.84/1.06  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.84/1.06  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.84/1.06  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.84/1.06  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.84/1.06  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.84/1.06  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.84/1.06  thf(sk_C_type, type, sk_C: $i).
% 0.84/1.06  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.84/1.06  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.84/1.06  thf(d4_enumset1, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.84/1.06     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.84/1.06       ( ![H:$i]:
% 0.84/1.06         ( ( r2_hidden @ H @ G ) <=>
% 0.84/1.06           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 0.84/1.06                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 0.84/1.06  thf(zf_stmt_0, axiom,
% 0.84/1.06    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.84/1.06     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 0.84/1.06       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 0.84/1.06         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 0.84/1.06  thf('0', plain,
% 0.84/1.06      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.84/1.06         ((zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44)
% 0.84/1.06          | ((X38) = (X39))
% 0.84/1.06          | ((X38) = (X40))
% 0.84/1.06          | ((X38) = (X41))
% 0.84/1.06          | ((X38) = (X42))
% 0.84/1.06          | ((X38) = (X43))
% 0.84/1.06          | ((X38) = (X44)))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf(t65_funct_2, conjecture,
% 0.84/1.06    (![A:$i,B:$i,C:$i,D:$i]:
% 0.84/1.06     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.84/1.06         ( m1_subset_1 @
% 0.84/1.06           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.84/1.06       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.84/1.06  thf(zf_stmt_1, negated_conjecture,
% 0.84/1.06    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.84/1.06        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.84/1.06            ( m1_subset_1 @
% 0.84/1.06              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.84/1.06          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.84/1.06    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.84/1.06  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.84/1.06  thf('2', plain,
% 0.84/1.06      ((m1_subset_1 @ sk_D_1 @ 
% 0.84/1.06        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.84/1.06  thf(t7_funct_2, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i,D:$i]:
% 0.84/1.06     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.84/1.06         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.06       ( ( r2_hidden @ C @ A ) =>
% 0.84/1.06         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.84/1.06           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.84/1.06  thf('3', plain,
% 0.84/1.06      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X58 @ X59)
% 0.84/1.06          | ((X60) = (k1_xboole_0))
% 0.84/1.06          | ~ (v1_funct_1 @ X61)
% 0.84/1.06          | ~ (v1_funct_2 @ X61 @ X59 @ X60)
% 0.84/1.06          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60)))
% 0.84/1.06          | (r2_hidden @ (k1_funct_1 @ X61 @ X58) @ X60))),
% 0.84/1.06      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.84/1.06  thf('4', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B_1))
% 0.84/1.06          | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.84/1.06          | ~ (v1_funct_1 @ sk_D_1)
% 0.84/1.06          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.84/1.06          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.84/1.06      inference('sup-', [status(thm)], ['2', '3'])).
% 0.84/1.06  thf('5', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.84/1.06  thf('6', plain, ((v1_funct_1 @ sk_D_1)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.84/1.06  thf('7', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B_1))
% 0.84/1.06          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.84/1.06          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.84/1.06      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.84/1.06  thf(t20_zfmisc_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.84/1.06         ( k1_tarski @ A ) ) <=>
% 0.84/1.06       ( ( A ) != ( B ) ) ))).
% 0.84/1.06  thf('8', plain,
% 0.84/1.06      (![X34 : $i, X35 : $i]:
% 0.84/1.06         (((X35) != (X34))
% 0.84/1.06          | ((k4_xboole_0 @ (k1_tarski @ X35) @ (k1_tarski @ X34))
% 0.84/1.06              != (k1_tarski @ X35)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.84/1.06  thf('9', plain,
% 0.84/1.06      (![X34 : $i]:
% 0.84/1.06         ((k4_xboole_0 @ (k1_tarski @ X34) @ (k1_tarski @ X34))
% 0.84/1.06           != (k1_tarski @ X34))),
% 0.84/1.06      inference('simplify', [status(thm)], ['8'])).
% 0.84/1.06  thf(t9_mcart_1, axiom,
% 0.84/1.06    (![A:$i]:
% 0.84/1.06     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.84/1.06          ( ![B:$i]:
% 0.84/1.06            ( ~( ( r2_hidden @ B @ A ) & 
% 0.84/1.06                 ( ![C:$i,D:$i]:
% 0.84/1.06                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.84/1.06                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.84/1.06  thf('10', plain,
% 0.84/1.06      (![X55 : $i]:
% 0.84/1.06         (((X55) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X55) @ X55))),
% 0.84/1.06      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.84/1.06  thf(d5_xboole_0, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.84/1.06       ( ![D:$i]:
% 0.84/1.06         ( ( r2_hidden @ D @ C ) <=>
% 0.84/1.06           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.84/1.06  thf('11', plain,
% 0.84/1.06      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X4 @ X3)
% 0.84/1.06          | (r2_hidden @ X4 @ X1)
% 0.84/1.06          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.84/1.06      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.84/1.06  thf('12', plain,
% 0.84/1.06      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.84/1.06         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.84/1.06      inference('simplify', [status(thm)], ['11'])).
% 0.84/1.06  thf('13', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.84/1.06          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.84/1.06      inference('sup-', [status(thm)], ['10', '12'])).
% 0.84/1.06  thf('14', plain,
% 0.84/1.06      (![X55 : $i]:
% 0.84/1.06         (((X55) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X55) @ X55))),
% 0.84/1.06      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.84/1.06  thf('15', plain,
% 0.84/1.06      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X4 @ X3)
% 0.84/1.06          | ~ (r2_hidden @ X4 @ X2)
% 0.84/1.06          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.84/1.06      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.84/1.06  thf('16', plain,
% 0.84/1.06      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X4 @ X2)
% 0.84/1.06          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.84/1.06      inference('simplify', [status(thm)], ['15'])).
% 0.84/1.06  thf('17', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.84/1.06          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['14', '16'])).
% 0.84/1.06  thf('18', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.84/1.06          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['13', '17'])).
% 0.84/1.06  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.84/1.06      inference('simplify', [status(thm)], ['18'])).
% 0.84/1.06  thf('20', plain, (![X34 : $i]: ((k1_xboole_0) != (k1_tarski @ X34))),
% 0.84/1.06      inference('demod', [status(thm)], ['9', '19'])).
% 0.84/1.06  thf('21', plain,
% 0.84/1.06      (![X0 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X0 @ sk_A)
% 0.84/1.06          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B_1)))),
% 0.84/1.06      inference('clc', [status(thm)], ['7', '20'])).
% 0.84/1.06  thf('22', plain,
% 0.84/1.06      ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C) @ (k1_tarski @ sk_B_1))),
% 0.84/1.06      inference('sup-', [status(thm)], ['1', '21'])).
% 0.84/1.06  thf(t69_enumset1, axiom,
% 0.84/1.06    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.84/1.06  thf('23', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.84/1.06      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.84/1.06  thf(t70_enumset1, axiom,
% 0.84/1.06    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.84/1.06  thf('24', plain,
% 0.84/1.06      (![X7 : $i, X8 : $i]:
% 0.84/1.06         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 0.84/1.06      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.84/1.06  thf(t71_enumset1, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.84/1.06  thf('25', plain,
% 0.84/1.06      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.84/1.06         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 0.84/1.06      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.84/1.06  thf(t72_enumset1, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i,D:$i]:
% 0.84/1.06     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.84/1.06  thf('26', plain,
% 0.84/1.06      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.84/1.06         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 0.84/1.06           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 0.84/1.06      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.84/1.06  thf(t73_enumset1, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.84/1.06     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.84/1.06       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.84/1.06  thf('27', plain,
% 0.84/1.06      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.84/1.06         ((k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.84/1.06           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.84/1.06      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.84/1.06  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 0.84/1.06  thf(zf_stmt_3, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.84/1.06     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.84/1.06       ( ![H:$i]:
% 0.84/1.06         ( ( r2_hidden @ H @ G ) <=>
% 0.84/1.06           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.84/1.06  thf('28', plain,
% 0.84/1.06      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, 
% 0.84/1.06         X53 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X53 @ X52)
% 0.84/1.06          | ~ (zip_tseitin_0 @ X53 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51)
% 0.84/1.06          | ((X52) != (k4_enumset1 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46)))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.84/1.06  thf('29', plain,
% 0.84/1.06      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X53 : $i]:
% 0.84/1.06         (~ (zip_tseitin_0 @ X53 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51)
% 0.84/1.06          | ~ (r2_hidden @ X53 @ 
% 0.84/1.06               (k4_enumset1 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46)))),
% 0.84/1.06      inference('simplify', [status(thm)], ['28'])).
% 0.84/1.06  thf('30', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.84/1.06          | ~ (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 0.84/1.06      inference('sup-', [status(thm)], ['27', '29'])).
% 0.84/1.06  thf('31', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.84/1.06          | ~ (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 @ X3))),
% 0.84/1.06      inference('sup-', [status(thm)], ['26', '30'])).
% 0.84/1.06  thf('32', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.84/1.06          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 @ X2))),
% 0.84/1.06      inference('sup-', [status(thm)], ['25', '31'])).
% 0.84/1.06  thf('33', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.84/1.06          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 @ X1))),
% 0.84/1.06      inference('sup-', [status(thm)], ['24', '32'])).
% 0.84/1.06  thf('34', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.84/1.06          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.84/1.06      inference('sup-', [status(thm)], ['23', '33'])).
% 0.84/1.06  thf('35', plain,
% 0.84/1.06      (~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D_1 @ sk_C) @ sk_B_1 @ sk_B_1 @ 
% 0.84/1.06          sk_B_1 @ sk_B_1 @ sk_B_1 @ sk_B_1)),
% 0.84/1.06      inference('sup-', [status(thm)], ['22', '34'])).
% 0.84/1.06  thf('36', plain,
% 0.84/1.06      ((((k1_funct_1 @ sk_D_1 @ sk_C) = (sk_B_1))
% 0.84/1.06        | ((k1_funct_1 @ sk_D_1 @ sk_C) = (sk_B_1))
% 0.84/1.06        | ((k1_funct_1 @ sk_D_1 @ sk_C) = (sk_B_1))
% 0.84/1.06        | ((k1_funct_1 @ sk_D_1 @ sk_C) = (sk_B_1))
% 0.84/1.06        | ((k1_funct_1 @ sk_D_1 @ sk_C) = (sk_B_1))
% 0.84/1.06        | ((k1_funct_1 @ sk_D_1 @ sk_C) = (sk_B_1)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['0', '35'])).
% 0.84/1.06  thf('37', plain, (((k1_funct_1 @ sk_D_1 @ sk_C) = (sk_B_1))),
% 0.84/1.06      inference('simplify', [status(thm)], ['36'])).
% 0.84/1.06  thf('38', plain, (((k1_funct_1 @ sk_D_1 @ sk_C) != (sk_B_1))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.84/1.06  thf('39', plain, ($false),
% 0.84/1.06      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.84/1.06  
% 0.84/1.06  % SZS output end Refutation
% 0.84/1.06  
% 0.92/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
