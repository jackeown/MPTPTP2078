%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zjhZOqZjvm

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  68 expanded)
%              Number of leaves         :   29 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  439 ( 621 expanded)
%              Number of equality atoms :   44 (  53 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(d2_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( ( F != D )
              & ( F != C )
              & ( F != B )
              & ( F != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf('0',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 )
      | ( X38 = X39 )
      | ( X38 = X40 )
      | ( X38 = X41 )
      | ( X38 = X42 ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( r2_hidden @ X53 @ X54 )
      | ( X55 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_funct_2 @ X56 @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X56 @ X53 ) @ X55 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('9',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33 != X32 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X32 ) )
       != ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('10',plain,(
    ! [X32: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X32 ) )
     != ( k1_tarski @ X32 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf(t22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X35 ) @ ( k2_tarski @ X35 @ X36 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t22_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['7','13'])).

thf('15',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X3 @ X3 @ X4 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X5 @ X5 @ X6 @ X7 )
      = ( k1_enumset1 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X49 @ X48 )
      | ~ ( zip_tseitin_0 @ X49 @ X44 @ X45 @ X46 @ X47 )
      | ( X48
       != ( k2_enumset1 @ X47 @ X46 @ X45 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X49: $i] :
      ( ~ ( zip_tseitin_0 @ X49 @ X44 @ X45 @ X46 @ X47 )
      | ~ ( r2_hidden @ X49 @ ( k2_enumset1 @ X47 @ X46 @ X45 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B ) ),
    inference('sup-',[status(thm)],['0','24'])).

thf('26',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C )
    = sk_B ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ( k1_funct_1 @ sk_D @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zjhZOqZjvm
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:21:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 95 iterations in 0.040s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.49  thf(d2_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.49     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.20/0.49       ( ![F:$i]:
% 0.20/0.49         ( ( r2_hidden @ F @ E ) <=>
% 0.20/0.49           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.20/0.49                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, axiom,
% 0.20/0.49    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.20/0.49       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.20/0.49         ( ( F ) != ( D ) ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.49         ((zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42)
% 0.20/0.49          | ((X38) = (X39))
% 0.20/0.49          | ((X38) = (X40))
% 0.20/0.49          | ((X38) = (X41))
% 0.20/0.49          | ((X38) = (X42)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t65_funct_2, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.49         ( m1_subset_1 @
% 0.20/0.49           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.49       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_1, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.49            ( m1_subset_1 @
% 0.20/0.49              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.49          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.20/0.49  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ 
% 0.20/0.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.49  thf(t7_funct_2, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.49       ( ( r2_hidden @ C @ A ) =>
% 0.20/0.49         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.49           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X53 @ X54)
% 0.20/0.49          | ((X55) = (k1_xboole_0))
% 0.20/0.49          | ~ (v1_funct_1 @ X56)
% 0.20/0.49          | ~ (v1_funct_2 @ X56 @ X54 @ X55)
% 0.20/0.49          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 0.20/0.49          | (r2_hidden @ (k1_funct_1 @ X56 @ X53) @ X55))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.20/0.49          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.49          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.49          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.49  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.20/0.49          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.49  thf(t69_enumset1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.49  thf('8', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf(t20_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.49         ( k1_tarski @ A ) ) <=>
% 0.20/0.49       ( ( A ) != ( B ) ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X32 : $i, X33 : $i]:
% 0.20/0.49         (((X33) != (X32))
% 0.20/0.49          | ((k4_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X32))
% 0.20/0.49              != (k1_tarski @ X33)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X32 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X32))
% 0.20/0.49           != (k1_tarski @ X32))),
% 0.20/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 0.20/0.49           != (k1_tarski @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '10'])).
% 0.20/0.49  thf(t22_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.20/0.49       ( k1_xboole_0 ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X35 : $i, X36 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ (k1_tarski @ X35) @ (k2_tarski @ X35 @ X36))
% 0.20/0.49           = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t22_zfmisc_1])).
% 0.20/0.49  thf('13', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.49          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B)))),
% 0.20/0.49      inference('clc', [status(thm)], ['7', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ (k1_tarski @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '14'])).
% 0.20/0.49  thf(t70_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         ((k1_enumset1 @ X3 @ X3 @ X4) = (k2_tarski @ X3 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.49  thf('17', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf(t71_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         ((k2_enumset1 @ X5 @ X5 @ X6 @ X7) = (k1_enumset1 @ X5 @ X6 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.49  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_3, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.49     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.20/0.49       ( ![F:$i]:
% 0.20/0.49         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X49 @ X48)
% 0.20/0.49          | ~ (zip_tseitin_0 @ X49 @ X44 @ X45 @ X46 @ X47)
% 0.20/0.49          | ((X48) != (k2_enumset1 @ X47 @ X46 @ X45 @ X44)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X49 : $i]:
% 0.20/0.49         (~ (zip_tseitin_0 @ X49 @ X44 @ X45 @ X46 @ X47)
% 0.20/0.49          | ~ (r2_hidden @ X49 @ (k2_enumset1 @ X47 @ X46 @ X45 @ X44)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.20/0.49          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.49          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B @ sk_B @ sk_B @ 
% 0.20/0.49          sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      ((((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.20/0.49        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.20/0.49        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.20/0.49        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '24'])).
% 0.20/0.49  thf('26', plain, (((k1_funct_1 @ sk_D @ sk_C) = (sk_B))),
% 0.20/0.49      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.49  thf('27', plain, (((k1_funct_1 @ sk_D @ sk_C) != (sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.49  thf('28', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
