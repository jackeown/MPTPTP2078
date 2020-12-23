%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YAvpZE6Adt

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:54 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   61 (  80 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  468 ( 772 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t41_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) )
      | ( ( k4_subset_1 @ X30 @ X29 @ X31 )
        = ( k2_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(t83_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_enumset1 @ X15 @ X15 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_enumset1])).

thf(t78_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X12 @ X13 @ X14 )
      = ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t78_enumset1])).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( r2_hidden @ X5 @ X9 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ ( k3_tarski @ X23 ) )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ( r1_tarski @ X3 @ ( k3_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','13'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X27 @ X26 @ X28 ) @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('26',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( r1_tarski @ X34 @ X32 )
      | ( r1_tarski @ ( k3_subset_1 @ X33 @ X32 ) @ ( k3_subset_1 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['6','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YAvpZE6Adt
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:18:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.05/1.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.05/1.24  % Solved by: fo/fo7.sh
% 1.05/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.24  % done 487 iterations in 0.780s
% 1.05/1.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.05/1.24  % SZS output start Refutation
% 1.05/1.24  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.05/1.24  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.24  thf(sk_C_type, type, sk_C: $i).
% 1.05/1.24  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.05/1.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.24  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.05/1.24  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.05/1.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.24  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.05/1.24  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.05/1.24  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.05/1.24  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.05/1.24  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.05/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.24  thf(t41_subset_1, conjecture,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.24       ( ![C:$i]:
% 1.05/1.24         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.24           ( r1_tarski @
% 1.05/1.24             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 1.05/1.24             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 1.05/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.24    (~( ![A:$i,B:$i]:
% 1.05/1.24        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.24          ( ![C:$i]:
% 1.05/1.24            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.24              ( r1_tarski @
% 1.05/1.24                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 1.05/1.24                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 1.05/1.24    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 1.05/1.24  thf('0', plain,
% 1.05/1.24      (~ (r1_tarski @ 
% 1.05/1.24          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C)) @ 
% 1.05/1.24          (k3_subset_1 @ sk_A @ sk_B))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(redefinition_k4_subset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.05/1.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.05/1.24       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.05/1.24  thf('3', plain,
% 1.05/1.24      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 1.05/1.24          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30))
% 1.05/1.24          | ((k4_subset_1 @ X30 @ X29 @ X31) = (k2_xboole_0 @ X29 @ X31)))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.05/1.24  thf('4', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 1.05/1.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['2', '3'])).
% 1.05/1.24  thf('5', plain,
% 1.05/1.24      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_B @ sk_C))),
% 1.05/1.24      inference('sup-', [status(thm)], ['1', '4'])).
% 1.05/1.24  thf('6', plain,
% 1.05/1.24      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 1.05/1.24          (k3_subset_1 @ sk_A @ sk_B))),
% 1.05/1.24      inference('demod', [status(thm)], ['0', '5'])).
% 1.05/1.24  thf(t83_enumset1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( k3_enumset1 @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.05/1.24  thf('7', plain,
% 1.05/1.24      (![X15 : $i, X16 : $i]:
% 1.05/1.24         ((k3_enumset1 @ X15 @ X15 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 1.05/1.24      inference('cnf', [status(esa)], [t83_enumset1])).
% 1.05/1.24  thf(t78_enumset1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( k3_enumset1 @ A @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.05/1.24  thf('8', plain,
% 1.05/1.24      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.05/1.24         ((k3_enumset1 @ X12 @ X12 @ X12 @ X13 @ X14)
% 1.05/1.24           = (k1_enumset1 @ X12 @ X13 @ X14))),
% 1.05/1.24      inference('cnf', [status(esa)], [t78_enumset1])).
% 1.05/1.24  thf('9', plain,
% 1.05/1.24      (![X15 : $i, X16 : $i]:
% 1.05/1.24         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 1.05/1.24      inference('demod', [status(thm)], ['7', '8'])).
% 1.05/1.24  thf(d1_enumset1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.24     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.05/1.24       ( ![E:$i]:
% 1.05/1.24         ( ( r2_hidden @ E @ D ) <=>
% 1.05/1.24           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.05/1.24  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.05/1.24  thf(zf_stmt_2, axiom,
% 1.05/1.24    (![E:$i,C:$i,B:$i,A:$i]:
% 1.05/1.24     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.05/1.24       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.05/1.24  thf(zf_stmt_3, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.24     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.05/1.24       ( ![E:$i]:
% 1.05/1.24         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.05/1.24  thf('10', plain,
% 1.05/1.24      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.05/1.24         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 1.05/1.24          | (r2_hidden @ X5 @ X9)
% 1.05/1.24          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.05/1.24  thf('11', plain,
% 1.05/1.24      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.05/1.24         ((r2_hidden @ X5 @ (k1_enumset1 @ X8 @ X7 @ X6))
% 1.05/1.24          | (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8))),
% 1.05/1.24      inference('simplify', [status(thm)], ['10'])).
% 1.05/1.24  thf(l49_zfmisc_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 1.05/1.24  thf('12', plain,
% 1.05/1.24      (![X22 : $i, X23 : $i]:
% 1.05/1.24         ((r1_tarski @ X22 @ (k3_tarski @ X23)) | ~ (r2_hidden @ X22 @ X23))),
% 1.05/1.24      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 1.05/1.24  thf('13', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.05/1.24         ((zip_tseitin_0 @ X3 @ X0 @ X1 @ X2)
% 1.05/1.24          | (r1_tarski @ X3 @ (k3_tarski @ (k1_enumset1 @ X2 @ X1 @ X0))))),
% 1.05/1.24      inference('sup-', [status(thm)], ['11', '12'])).
% 1.05/1.24  thf('14', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.24         ((r1_tarski @ X2 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))
% 1.05/1.24          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.05/1.24      inference('sup+', [status(thm)], ['9', '13'])).
% 1.05/1.24  thf(l51_zfmisc_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.05/1.24  thf('15', plain,
% 1.05/1.24      (![X24 : $i, X25 : $i]:
% 1.05/1.24         ((k3_tarski @ (k2_tarski @ X24 @ X25)) = (k2_xboole_0 @ X24 @ X25))),
% 1.05/1.24      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.05/1.24  thf('16', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.24         ((r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 1.05/1.24          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.05/1.24      inference('demod', [status(thm)], ['14', '15'])).
% 1.05/1.24  thf('17', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.05/1.24         (((X1) != (X0)) | ~ (zip_tseitin_0 @ X1 @ X2 @ X3 @ X0))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.05/1.24  thf('18', plain,
% 1.05/1.24      (![X0 : $i, X2 : $i, X3 : $i]: ~ (zip_tseitin_0 @ X0 @ X2 @ X3 @ X0)),
% 1.05/1.24      inference('simplify', [status(thm)], ['17'])).
% 1.05/1.24  thf('19', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 1.05/1.24      inference('sup-', [status(thm)], ['16', '18'])).
% 1.05/1.24  thf('20', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('21', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(dt_k4_subset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.05/1.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.05/1.24       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.05/1.24  thf('22', plain,
% 1.05/1.24      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 1.05/1.24          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27))
% 1.05/1.24          | (m1_subset_1 @ (k4_subset_1 @ X27 @ X26 @ X28) @ 
% 1.05/1.24             (k1_zfmisc_1 @ X27)))),
% 1.05/1.24      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 1.05/1.24  thf('23', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ X0) @ 
% 1.05/1.24           (k1_zfmisc_1 @ sk_A))
% 1.05/1.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['21', '22'])).
% 1.05/1.24  thf('24', plain,
% 1.05/1.24      ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 1.05/1.24      inference('sup-', [status(thm)], ['20', '23'])).
% 1.05/1.24  thf('25', plain,
% 1.05/1.24      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_B @ sk_C))),
% 1.05/1.24      inference('sup-', [status(thm)], ['1', '4'])).
% 1.05/1.24  thf('26', plain,
% 1.05/1.24      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 1.05/1.24      inference('demod', [status(thm)], ['24', '25'])).
% 1.05/1.24  thf(t31_subset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.24       ( ![C:$i]:
% 1.05/1.24         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.24           ( ( r1_tarski @ B @ C ) <=>
% 1.05/1.24             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 1.05/1.24  thf('27', plain,
% 1.05/1.24      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 1.05/1.24          | ~ (r1_tarski @ X34 @ X32)
% 1.05/1.24          | (r1_tarski @ (k3_subset_1 @ X33 @ X32) @ (k3_subset_1 @ X33 @ X34))
% 1.05/1.24          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 1.05/1.24      inference('cnf', [status(esa)], [t31_subset_1])).
% 1.05/1.24  thf('28', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 1.05/1.24          | (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 1.05/1.24             (k3_subset_1 @ sk_A @ X0))
% 1.05/1.24          | ~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['26', '27'])).
% 1.05/1.24  thf('29', plain,
% 1.05/1.24      (((r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 1.05/1.24         (k3_subset_1 @ sk_A @ sk_B))
% 1.05/1.24        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['19', '28'])).
% 1.05/1.24  thf('30', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('31', plain,
% 1.05/1.24      ((r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 1.05/1.24        (k3_subset_1 @ sk_A @ sk_B))),
% 1.05/1.24      inference('demod', [status(thm)], ['29', '30'])).
% 1.05/1.24  thf('32', plain, ($false), inference('demod', [status(thm)], ['6', '31'])).
% 1.05/1.24  
% 1.05/1.24  % SZS output end Refutation
% 1.05/1.24  
% 1.05/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
