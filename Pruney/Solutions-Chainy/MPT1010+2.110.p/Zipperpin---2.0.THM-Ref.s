%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RDjC2vc9vZ

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:28 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   64 (  72 expanded)
%              Number of leaves         :   33 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  408 ( 584 expanded)
%              Number of equality atoms :   36 (  44 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ( X39 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X40 @ X37 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B_1 ) )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( sk_B @ X33 ) @ ( k1_zfmisc_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( sk_B @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( sk_B @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('15',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X31 ) @ X32 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['7','16'])).

thf('18',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','17'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('19',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B_1 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B_1 )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B_1 )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C )
    = sk_B_1 ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ( k1_funct_1 @ sk_D @ sk_C )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RDjC2vc9vZ
% 0.15/0.38  % Computer   : n002.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 18:01:22 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.25/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.52  % Solved by: fo/fo7.sh
% 0.25/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.52  % done 57 iterations in 0.025s
% 0.25/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.52  % SZS output start Refutation
% 0.25/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.25/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.25/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.25/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.25/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.25/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.25/0.52  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.25/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.25/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.25/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.25/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.25/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.25/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.25/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.25/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.52  thf(d1_enumset1, axiom,
% 0.25/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.52     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.25/0.52       ( ![E:$i]:
% 0.25/0.52         ( ( r2_hidden @ E @ D ) <=>
% 0.25/0.52           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.25/0.52  thf(zf_stmt_0, axiom,
% 0.25/0.52    (![E:$i,C:$i,B:$i,A:$i]:
% 0.25/0.52     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.25/0.52       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.25/0.52  thf('0', plain,
% 0.25/0.52      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.25/0.52         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.25/0.52          | ((X5) = (X6))
% 0.25/0.52          | ((X5) = (X7))
% 0.25/0.52          | ((X5) = (X8)))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf(t65_funct_2, conjecture,
% 0.25/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.25/0.52         ( m1_subset_1 @
% 0.25/0.52           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.25/0.52       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.25/0.52  thf(zf_stmt_1, negated_conjecture,
% 0.25/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.52        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.25/0.52            ( m1_subset_1 @
% 0.25/0.52              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.25/0.52          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.25/0.52    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.25/0.52  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.25/0.52  thf('2', plain,
% 0.25/0.52      ((m1_subset_1 @ sk_D @ 
% 0.25/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.25/0.52  thf(t7_funct_2, axiom,
% 0.25/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.25/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.25/0.52       ( ( r2_hidden @ C @ A ) =>
% 0.25/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.25/0.52           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.25/0.52  thf('3', plain,
% 0.25/0.52      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.25/0.52         (~ (r2_hidden @ X37 @ X38)
% 0.25/0.52          | ((X39) = (k1_xboole_0))
% 0.25/0.52          | ~ (v1_funct_1 @ X40)
% 0.25/0.52          | ~ (v1_funct_2 @ X40 @ X38 @ X39)
% 0.25/0.52          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.25/0.52          | (r2_hidden @ (k1_funct_1 @ X40 @ X37) @ X39))),
% 0.25/0.52      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.25/0.52  thf('4', plain,
% 0.25/0.52      (![X0 : $i]:
% 0.25/0.52         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B_1))
% 0.25/0.52          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B_1))
% 0.25/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.25/0.52          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.25/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.25/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.25/0.52  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.25/0.52  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.25/0.52  thf('7', plain,
% 0.25/0.52      (![X0 : $i]:
% 0.25/0.52         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B_1))
% 0.25/0.52          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.25/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.25/0.52      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.25/0.52  thf(rc3_subset_1, axiom,
% 0.25/0.52    (![A:$i]:
% 0.25/0.52     ( ?[B:$i]:
% 0.25/0.52       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.25/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.25/0.52  thf('8', plain,
% 0.25/0.52      (![X33 : $i]: (m1_subset_1 @ (sk_B @ X33) @ (k1_zfmisc_1 @ X33))),
% 0.25/0.52      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.25/0.52  thf(t3_subset, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.25/0.52  thf('9', plain,
% 0.25/0.52      (![X34 : $i, X35 : $i]:
% 0.25/0.52         ((r1_tarski @ X34 @ X35) | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.25/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.25/0.52  thf('10', plain, (![X0 : $i]: (r1_tarski @ (sk_B @ X0) @ X0)),
% 0.25/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.25/0.52  thf(t12_xboole_1, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.25/0.52  thf('11', plain,
% 0.25/0.52      (![X2 : $i, X3 : $i]:
% 0.25/0.52         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.25/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.25/0.52  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ (sk_B @ X0) @ X0) = (X0))),
% 0.25/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.25/0.52  thf(commutativity_k2_xboole_0, axiom,
% 0.25/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.25/0.52  thf('13', plain,
% 0.25/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.25/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.25/0.52  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ (sk_B @ X0)) = (X0))),
% 0.25/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.25/0.52  thf(t49_zfmisc_1, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.25/0.52  thf('15', plain,
% 0.25/0.52      (![X31 : $i, X32 : $i]:
% 0.25/0.52         ((k2_xboole_0 @ (k1_tarski @ X31) @ X32) != (k1_xboole_0))),
% 0.25/0.52      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.25/0.52  thf('16', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.25/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.25/0.52  thf('17', plain,
% 0.25/0.52      (![X0 : $i]:
% 0.25/0.52         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B_1))
% 0.25/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.25/0.52      inference('simplify_reflect-', [status(thm)], ['7', '16'])).
% 0.25/0.52  thf('18', plain,
% 0.25/0.52      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ (k1_tarski @ sk_B_1))),
% 0.25/0.52      inference('sup-', [status(thm)], ['1', '17'])).
% 0.25/0.52  thf(t69_enumset1, axiom,
% 0.25/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.25/0.52  thf('19', plain,
% 0.25/0.52      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.25/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.25/0.52  thf(t70_enumset1, axiom,
% 0.25/0.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.25/0.52  thf('20', plain,
% 0.25/0.52      (![X17 : $i, X18 : $i]:
% 0.25/0.52         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.25/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.25/0.52  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.25/0.52  thf(zf_stmt_3, axiom,
% 0.25/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.52     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.25/0.52       ( ![E:$i]:
% 0.25/0.52         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.25/0.52  thf('21', plain,
% 0.25/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.25/0.52         (~ (r2_hidden @ X14 @ X13)
% 0.25/0.52          | ~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.25/0.52          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.25/0.52  thf('22', plain,
% 0.25/0.52      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.25/0.52         (~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.25/0.52          | ~ (r2_hidden @ X14 @ (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.25/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.25/0.52  thf('23', plain,
% 0.25/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.52         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.25/0.52          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.25/0.52      inference('sup-', [status(thm)], ['20', '22'])).
% 0.25/0.52  thf('24', plain,
% 0.25/0.52      (![X0 : $i, X1 : $i]:
% 0.25/0.52         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.25/0.52          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.25/0.52      inference('sup-', [status(thm)], ['19', '23'])).
% 0.25/0.52  thf('25', plain,
% 0.25/0.52      (~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B_1 @ sk_B_1 @ sk_B_1)),
% 0.25/0.52      inference('sup-', [status(thm)], ['18', '24'])).
% 0.25/0.52  thf('26', plain,
% 0.25/0.52      ((((k1_funct_1 @ sk_D @ sk_C) = (sk_B_1))
% 0.25/0.52        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B_1))
% 0.25/0.52        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B_1)))),
% 0.25/0.52      inference('sup-', [status(thm)], ['0', '25'])).
% 0.25/0.52  thf('27', plain, (((k1_funct_1 @ sk_D @ sk_C) = (sk_B_1))),
% 0.25/0.52      inference('simplify', [status(thm)], ['26'])).
% 0.25/0.52  thf('28', plain, (((k1_funct_1 @ sk_D @ sk_C) != (sk_B_1))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.25/0.52  thf('29', plain, ($false),
% 0.25/0.52      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.25/0.52  
% 0.25/0.52  % SZS output end Refutation
% 0.25/0.52  
% 0.25/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
