%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.goBiGnlfN9

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 157 expanded)
%              Number of leaves         :   35 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  519 (1769 expanded)
%              Number of equality atoms :   61 ( 152 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 )
      | ( X35 = X36 )
      | ( X35 = X37 )
      | ( X35 = X38 )
      | ( X35 = X39 ) ) ),
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
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ( X53 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_funct_2 @ X54 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X54 @ X51 ) @ X53 ) ) ),
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

thf('8',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X6 @ X6 @ X7 @ X8 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
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

thf('13',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X46 @ X45 )
      | ~ ( zip_tseitin_0 @ X46 @ X41 @ X42 @ X43 @ X44 )
      | ( X45
       != ( k2_enumset1 @ X44 @ X43 @ X42 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X46 @ X41 @ X42 @ X43 @ X44 )
      | ~ ( r2_hidden @ X46 @ ( k2_enumset1 @ X44 @ X43 @ X42 @ X41 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','17'])).

thf('19',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ( k1_funct_1 @ sk_D @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('22',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32 != X31 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X31 ) )
       != ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('23',plain,(
    ! [X31: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X31 ) @ ( k1_tarski @ X31 ) )
     != ( k1_tarski @ X31 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('25',plain,(
    ! [X48: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X48 ) )
      = X48 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X31: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X31 ) @ ( k1_tarski @ X31 ) )
     != ( k1_tarski @ X31 ) ) ),
    inference(demod,[status(thm)],['23','30'])).

thf('32',plain,(
    ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['21','31'])).

thf('33',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('35',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('36',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.goBiGnlfN9
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:42:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 96 iterations in 0.043s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.51  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.22/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.51  thf(d2_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.51     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.22/0.51       ( ![F:$i]:
% 0.22/0.51         ( ( r2_hidden @ F @ E ) <=>
% 0.22/0.51           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.22/0.51                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, axiom,
% 0.22/0.51    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.22/0.51     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.22/0.51       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.22/0.51         ( ( F ) != ( D ) ) ) ))).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.22/0.51         ((zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39)
% 0.22/0.51          | ((X35) = (X36))
% 0.22/0.51          | ((X35) = (X37))
% 0.22/0.51          | ((X35) = (X38))
% 0.22/0.51          | ((X35) = (X39)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t65_funct_2, conjecture,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.22/0.51         ( m1_subset_1 @
% 0.22/0.51           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.22/0.51       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_1, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.22/0.51            ( m1_subset_1 @
% 0.22/0.51              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.22/0.51          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.22/0.51  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_D @ 
% 0.22/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.51  thf(t7_funct_2, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.51       ( ( r2_hidden @ C @ A ) =>
% 0.22/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.51           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X51 @ X52)
% 0.22/0.51          | ((X53) = (k1_xboole_0))
% 0.22/0.51          | ~ (v1_funct_1 @ X54)
% 0.22/0.51          | ~ (v1_funct_2 @ X54 @ X52 @ X53)
% 0.22/0.51          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 0.22/0.51          | (r2_hidden @ (k1_funct_1 @ X54 @ X51) @ X53))),
% 0.22/0.51      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.22/0.51          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.22/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.51          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.22/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.51  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.22/0.51          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.22/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.22/0.51        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ (k1_tarski @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '7'])).
% 0.22/0.51  thf(t70_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X4 : $i, X5 : $i]:
% 0.22/0.51         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.51  thf(t69_enumset1, axiom,
% 0.22/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.51  thf('10', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf(t71_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.51         ((k2_enumset1 @ X6 @ X6 @ X7 @ X8) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 0.22/0.51      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.22/0.51  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.22/0.51  thf(zf_stmt_3, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.51     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.22/0.51       ( ![F:$i]:
% 0.22/0.51         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X46 @ X45)
% 0.22/0.51          | ~ (zip_tseitin_0 @ X46 @ X41 @ X42 @ X43 @ X44)
% 0.22/0.51          | ((X45) != (k2_enumset1 @ X44 @ X43 @ X42 @ X41)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X46 : $i]:
% 0.22/0.51         (~ (zip_tseitin_0 @ X46 @ X41 @ X42 @ X43 @ X44)
% 0.22/0.51          | ~ (r2_hidden @ X46 @ (k2_enumset1 @ X44 @ X43 @ X42 @ X41)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.22/0.51          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 0.22/0.51      inference('sup-', [status(thm)], ['12', '14'])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.22/0.51          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['11', '15'])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.22/0.51        | ~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B @ sk_B @ sk_B @ 
% 0.22/0.51             sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['8', '16'])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      ((((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.22/0.51        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.22/0.51        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.22/0.51        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.22/0.51        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '17'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.22/0.51        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.51  thf('20', plain, (((k1_funct_1 @ sk_D @ sk_C) != (sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.51  thf('21', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf(t20_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.51         ( k1_tarski @ A ) ) <=>
% 0.22/0.51       ( ( A ) != ( B ) ) ))).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X31 : $i, X32 : $i]:
% 0.22/0.51         (((X32) != (X31))
% 0.22/0.51          | ((k4_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X31))
% 0.22/0.51              != (k1_tarski @ X32)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (![X31 : $i]:
% 0.22/0.51         ((k4_xboole_0 @ (k1_tarski @ X31) @ (k1_tarski @ X31))
% 0.22/0.51           != (k1_tarski @ X31))),
% 0.22/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.22/0.51  thf('24', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.51  thf(t11_setfam_1, axiom,
% 0.22/0.51    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.22/0.51  thf('25', plain, (![X48 : $i]: ((k1_setfam_1 @ (k1_tarski @ X48)) = (X48))),
% 0.22/0.51      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.51  thf(t12_setfam_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      (![X49 : $i, X50 : $i]:
% 0.22/0.51         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 0.22/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.51  thf('28', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.51  thf(t100_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.51           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['28', '29'])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      (![X31 : $i]:
% 0.22/0.51         ((k5_xboole_0 @ (k1_tarski @ X31) @ (k1_tarski @ X31))
% 0.22/0.51           != (k1_tarski @ X31))),
% 0.22/0.51      inference('demod', [status(thm)], ['23', '30'])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) != (k1_tarski @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['21', '31'])).
% 0.22/0.51  thf('33', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf(t5_boole, axiom,
% 0.22/0.51    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.51  thf('34', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.51  thf('35', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.22/0.51      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf('36', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.51      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.22/0.51  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
