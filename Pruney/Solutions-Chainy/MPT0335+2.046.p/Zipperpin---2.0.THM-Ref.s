%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lexITQeJCh

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:18 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   55 (  66 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  487 ( 671 expanded)
%              Number of equality atoms :   51 (  68 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k3_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( X14 = X15 )
      | ( X14 = X16 )
      | ( X14 = X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
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

thf('13',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( zip_tseitin_0 @ X23 @ X19 @ X20 @ X21 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X19 @ X20 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) @ X1 ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['7','27'])).

thf('29',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['6','28'])).

thf('30',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lexITQeJCh
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.22/2.40  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.22/2.40  % Solved by: fo/fo7.sh
% 2.22/2.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.22/2.40  % done 1889 iterations in 1.947s
% 2.22/2.40  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.22/2.40  % SZS output start Refutation
% 2.22/2.40  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.22/2.40  thf(sk_A_type, type, sk_A: $i).
% 2.22/2.40  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.22/2.40  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.22/2.40  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 2.22/2.40  thf(sk_C_type, type, sk_C: $i).
% 2.22/2.40  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.22/2.40  thf(sk_D_1_type, type, sk_D_1: $i).
% 2.22/2.40  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.22/2.40  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.22/2.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.22/2.40  thf(sk_B_type, type, sk_B: $i).
% 2.22/2.40  thf(t148_zfmisc_1, conjecture,
% 2.22/2.40    (![A:$i,B:$i,C:$i,D:$i]:
% 2.22/2.40     ( ( ( r1_tarski @ A @ B ) & 
% 2.22/2.40         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 2.22/2.40         ( r2_hidden @ D @ A ) ) =>
% 2.22/2.40       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 2.22/2.40  thf(zf_stmt_0, negated_conjecture,
% 2.22/2.40    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.22/2.40        ( ( ( r1_tarski @ A @ B ) & 
% 2.22/2.40            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 2.22/2.40            ( r2_hidden @ D @ A ) ) =>
% 2.22/2.40          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 2.22/2.40    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 2.22/2.40  thf('0', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D_1))),
% 2.22/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.40  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 2.22/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.40  thf(t28_xboole_1, axiom,
% 2.22/2.40    (![A:$i,B:$i]:
% 2.22/2.40     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.22/2.40  thf('2', plain,
% 2.22/2.40      (![X9 : $i, X10 : $i]:
% 2.22/2.40         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 2.22/2.40      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.22/2.40  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 2.22/2.40      inference('sup-', [status(thm)], ['1', '2'])).
% 2.22/2.40  thf(t16_xboole_1, axiom,
% 2.22/2.40    (![A:$i,B:$i,C:$i]:
% 2.22/2.40     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 2.22/2.40       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 2.22/2.40  thf('4', plain,
% 2.22/2.40      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.22/2.40         ((k3_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ X8)
% 2.22/2.40           = (k3_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8)))),
% 2.22/2.40      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.22/2.40  thf('5', plain,
% 2.22/2.40      (![X0 : $i]:
% 2.22/2.40         ((k3_xboole_0 @ sk_A @ X0)
% 2.22/2.40           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 2.22/2.40      inference('sup+', [status(thm)], ['3', '4'])).
% 2.22/2.40  thf('6', plain,
% 2.22/2.40      (((k3_xboole_0 @ sk_A @ sk_C)
% 2.22/2.40         = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 2.22/2.40      inference('sup+', [status(thm)], ['0', '5'])).
% 2.22/2.40  thf('7', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 2.22/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.40  thf(d1_enumset1, axiom,
% 2.22/2.40    (![A:$i,B:$i,C:$i,D:$i]:
% 2.22/2.40     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.22/2.40       ( ![E:$i]:
% 2.22/2.40         ( ( r2_hidden @ E @ D ) <=>
% 2.22/2.40           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 2.22/2.40  thf(zf_stmt_1, axiom,
% 2.22/2.40    (![E:$i,C:$i,B:$i,A:$i]:
% 2.22/2.40     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 2.22/2.40       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 2.22/2.40  thf('8', plain,
% 2.22/2.40      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 2.22/2.40         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 2.22/2.40          | ((X14) = (X15))
% 2.22/2.40          | ((X14) = (X16))
% 2.22/2.40          | ((X14) = (X17)))),
% 2.22/2.40      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.40  thf(d4_xboole_0, axiom,
% 2.22/2.40    (![A:$i,B:$i,C:$i]:
% 2.22/2.40     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 2.22/2.40       ( ![D:$i]:
% 2.22/2.40         ( ( r2_hidden @ D @ C ) <=>
% 2.22/2.40           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.22/2.40  thf('9', plain,
% 2.22/2.40      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.22/2.40         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 2.22/2.40          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.22/2.40          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.22/2.40      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.22/2.40  thf('10', plain,
% 2.22/2.40      (![X0 : $i, X1 : $i]:
% 2.22/2.40         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.22/2.40          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.22/2.40      inference('eq_fact', [status(thm)], ['9'])).
% 2.22/2.40  thf(t69_enumset1, axiom,
% 2.22/2.40    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.22/2.40  thf('11', plain,
% 2.22/2.40      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 2.22/2.40      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.22/2.40  thf(t70_enumset1, axiom,
% 2.22/2.40    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.22/2.40  thf('12', plain,
% 2.22/2.40      (![X26 : $i, X27 : $i]:
% 2.22/2.40         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 2.22/2.40      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.22/2.40  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 2.22/2.40  thf(zf_stmt_3, axiom,
% 2.22/2.40    (![A:$i,B:$i,C:$i,D:$i]:
% 2.22/2.40     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.22/2.40       ( ![E:$i]:
% 2.22/2.40         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 2.22/2.40  thf('13', plain,
% 2.22/2.40      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 2.22/2.40         (~ (r2_hidden @ X23 @ X22)
% 2.22/2.40          | ~ (zip_tseitin_0 @ X23 @ X19 @ X20 @ X21)
% 2.22/2.40          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 2.22/2.40      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.22/2.40  thf('14', plain,
% 2.22/2.40      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 2.22/2.40         (~ (zip_tseitin_0 @ X23 @ X19 @ X20 @ X21)
% 2.22/2.40          | ~ (r2_hidden @ X23 @ (k1_enumset1 @ X21 @ X20 @ X19)))),
% 2.22/2.40      inference('simplify', [status(thm)], ['13'])).
% 2.22/2.40  thf('15', plain,
% 2.22/2.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.22/2.40         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.22/2.40          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 2.22/2.40      inference('sup-', [status(thm)], ['12', '14'])).
% 2.22/2.40  thf('16', plain,
% 2.22/2.40      (![X0 : $i, X1 : $i]:
% 2.22/2.40         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 2.22/2.40          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 2.22/2.40      inference('sup-', [status(thm)], ['11', '15'])).
% 2.22/2.40  thf('17', plain,
% 2.22/2.40      (![X0 : $i, X1 : $i]:
% 2.22/2.40         (((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 2.22/2.40          | ~ (zip_tseitin_0 @ 
% 2.22/2.40               (sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X0) @ X1) @ X0 @ X0 @ X0))),
% 2.22/2.40      inference('sup-', [status(thm)], ['10', '16'])).
% 2.22/2.40  thf('18', plain,
% 2.22/2.40      (![X0 : $i, X1 : $i]:
% 2.22/2.40         (((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X0) @ X1) = (X0))
% 2.22/2.40          | ((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X0) @ X1) = (X0))
% 2.22/2.40          | ((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X0) @ X1) = (X0))
% 2.22/2.40          | ((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 2.22/2.40      inference('sup-', [status(thm)], ['8', '17'])).
% 2.22/2.40  thf('19', plain,
% 2.22/2.40      (![X0 : $i, X1 : $i]:
% 2.22/2.40         (((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 2.22/2.40          | ((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X0) @ X1) = (X0)))),
% 2.22/2.40      inference('simplify', [status(thm)], ['18'])).
% 2.22/2.40  thf('20', plain,
% 2.22/2.40      (![X0 : $i, X1 : $i]:
% 2.22/2.40         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.22/2.40          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.22/2.40      inference('eq_fact', [status(thm)], ['9'])).
% 2.22/2.40  thf('21', plain,
% 2.22/2.40      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.22/2.40         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 2.22/2.40          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.22/2.40          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.22/2.40          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.22/2.40      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.22/2.40  thf('22', plain,
% 2.22/2.40      (![X0 : $i, X1 : $i]:
% 2.22/2.40         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 2.22/2.40          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.22/2.40          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 2.22/2.40          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.22/2.40      inference('sup-', [status(thm)], ['20', '21'])).
% 2.22/2.40  thf('23', plain,
% 2.22/2.40      (![X0 : $i, X1 : $i]:
% 2.22/2.40         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 2.22/2.40          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.22/2.40          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.22/2.40      inference('simplify', [status(thm)], ['22'])).
% 2.22/2.40  thf('24', plain,
% 2.22/2.40      (![X0 : $i, X1 : $i]:
% 2.22/2.40         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.22/2.40          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.22/2.40      inference('eq_fact', [status(thm)], ['9'])).
% 2.22/2.40  thf('25', plain,
% 2.22/2.40      (![X0 : $i, X1 : $i]:
% 2.22/2.40         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 2.22/2.40          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 2.22/2.40      inference('clc', [status(thm)], ['23', '24'])).
% 2.22/2.40  thf('26', plain,
% 2.22/2.40      (![X0 : $i, X1 : $i]:
% 2.22/2.40         (~ (r2_hidden @ X0 @ X1)
% 2.22/2.40          | ((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 2.22/2.40          | ((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 2.22/2.40      inference('sup-', [status(thm)], ['19', '25'])).
% 2.22/2.40  thf('27', plain,
% 2.22/2.40      (![X0 : $i, X1 : $i]:
% 2.22/2.40         (((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 2.22/2.40          | ~ (r2_hidden @ X0 @ X1))),
% 2.22/2.40      inference('simplify', [status(thm)], ['26'])).
% 2.22/2.40  thf('28', plain,
% 2.22/2.40      (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 2.22/2.40      inference('sup-', [status(thm)], ['7', '27'])).
% 2.22/2.40  thf('29', plain, (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_A @ sk_C))),
% 2.22/2.40      inference('sup+', [status(thm)], ['6', '28'])).
% 2.22/2.40  thf('30', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D_1))),
% 2.22/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.40  thf('31', plain, ($false),
% 2.22/2.40      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 2.22/2.40  
% 2.22/2.40  % SZS output end Refutation
% 2.22/2.40  
% 2.22/2.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
