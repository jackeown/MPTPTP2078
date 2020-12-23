%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vzAfrcpfWu

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:51 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 109 expanded)
%              Number of leaves         :   18 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  346 (1086 expanded)
%              Number of equality atoms :   45 ( 134 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t17_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( ( k2_mcart_1 @ A )
          = D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( ( k2_mcart_1 @ A )
            = D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_enumset1 @ X10 @ X10 @ X11 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_enumset1 @ sk_B @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_enumset1 @ X10 @ X10 @ X11 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t15_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )).

thf('4',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_mcart_1 @ X27 )
        = X26 )
      | ( ( k1_mcart_1 @ X27 )
        = X28 )
      | ~ ( r2_hidden @ X27 @ ( k2_zfmisc_1 @ ( k2_tarski @ X28 @ X26 ) @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t15_mcart_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ X2 ) )
      | ( ( k1_mcart_1 @ X3 )
        = X1 )
      | ( ( k1_mcart_1 @ X3 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_enumset1 @ sk_B @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X23 ) @ X25 )
      | ~ ( r2_hidden @ X23 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('11',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k4_xboole_0 @ X20 @ ( k1_tarski @ X22 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k2_mcart_1 @ sk_A )
        = X0 )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

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
    ! [X0: $i] :
      ( ( ( k2_mcart_1 @ sk_A )
        = X0 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D_1 ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('20',plain,
    ( ( sk_D_1 != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D_1 ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('23',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['21','22'])).

thf('24',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['8','23'])).

thf('25',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['25'])).

thf('28',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['21','27'])).

thf('29',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['26','28'])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['6','24','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vzAfrcpfWu
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:51:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.56/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.56/0.80  % Solved by: fo/fo7.sh
% 0.56/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.80  % done 547 iterations in 0.341s
% 0.56/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.56/0.80  % SZS output start Refutation
% 0.56/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.56/0.80  thf(sk_C_type, type, sk_C: $i).
% 0.56/0.80  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.56/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.56/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.56/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.56/0.80  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.56/0.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.56/0.80  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.56/0.80  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.56/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.80  thf(t17_mcart_1, conjecture,
% 0.56/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.80     ( ( r2_hidden @
% 0.56/0.80         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.56/0.80       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.56/0.80         ( ( k2_mcart_1 @ A ) = ( D ) ) ) ))).
% 0.56/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.80    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.80        ( ( r2_hidden @
% 0.56/0.80            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.56/0.80          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.56/0.80            ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) )),
% 0.56/0.80    inference('cnf.neg', [status(esa)], [t17_mcart_1])).
% 0.56/0.80  thf('0', plain,
% 0.56/0.80      ((r2_hidden @ sk_A @ 
% 0.56/0.80        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D_1)))),
% 0.56/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.80  thf(t70_enumset1, axiom,
% 0.56/0.80    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.56/0.80  thf('1', plain,
% 0.56/0.80      (![X10 : $i, X11 : $i]:
% 0.56/0.80         ((k1_enumset1 @ X10 @ X10 @ X11) = (k2_tarski @ X10 @ X11))),
% 0.56/0.80      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.56/0.80  thf('2', plain,
% 0.56/0.80      ((r2_hidden @ sk_A @ 
% 0.56/0.80        (k2_zfmisc_1 @ (k1_enumset1 @ sk_B @ sk_B @ sk_C) @ 
% 0.56/0.80         (k1_tarski @ sk_D_1)))),
% 0.56/0.80      inference('demod', [status(thm)], ['0', '1'])).
% 0.56/0.80  thf('3', plain,
% 0.56/0.80      (![X10 : $i, X11 : $i]:
% 0.56/0.80         ((k1_enumset1 @ X10 @ X10 @ X11) = (k2_tarski @ X10 @ X11))),
% 0.56/0.80      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.56/0.80  thf(t15_mcart_1, axiom,
% 0.56/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.80     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 0.56/0.80       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.56/0.80         ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ))).
% 0.56/0.80  thf('4', plain,
% 0.56/0.80      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.56/0.80         (((k1_mcart_1 @ X27) = (X26))
% 0.56/0.80          | ((k1_mcart_1 @ X27) = (X28))
% 0.56/0.80          | ~ (r2_hidden @ X27 @ (k2_zfmisc_1 @ (k2_tarski @ X28 @ X26) @ X29)))),
% 0.56/0.80      inference('cnf', [status(esa)], [t15_mcart_1])).
% 0.56/0.80  thf('5', plain,
% 0.56/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.56/0.80         (~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ (k1_enumset1 @ X1 @ X1 @ X0) @ X2))
% 0.56/0.80          | ((k1_mcart_1 @ X3) = (X1))
% 0.56/0.80          | ((k1_mcart_1 @ X3) = (X0)))),
% 0.56/0.80      inference('sup-', [status(thm)], ['3', '4'])).
% 0.56/0.80  thf('6', plain,
% 0.56/0.80      ((((k1_mcart_1 @ sk_A) = (sk_C)) | ((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.56/0.80      inference('sup-', [status(thm)], ['2', '5'])).
% 0.56/0.80  thf('7', plain,
% 0.56/0.80      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.56/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.80  thf('8', plain,
% 0.56/0.80      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.56/0.80         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.56/0.80      inference('split', [status(esa)], ['7'])).
% 0.56/0.80  thf('9', plain,
% 0.56/0.80      ((r2_hidden @ sk_A @ 
% 0.56/0.80        (k2_zfmisc_1 @ (k1_enumset1 @ sk_B @ sk_B @ sk_C) @ 
% 0.56/0.80         (k1_tarski @ sk_D_1)))),
% 0.56/0.80      inference('demod', [status(thm)], ['0', '1'])).
% 0.56/0.80  thf(t10_mcart_1, axiom,
% 0.56/0.80    (![A:$i,B:$i,C:$i]:
% 0.56/0.80     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.56/0.80       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.56/0.80         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.56/0.80  thf('10', plain,
% 0.56/0.80      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.56/0.80         ((r2_hidden @ (k2_mcart_1 @ X23) @ X25)
% 0.56/0.80          | ~ (r2_hidden @ X23 @ (k2_zfmisc_1 @ X24 @ X25)))),
% 0.56/0.80      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.56/0.80  thf('11', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_D_1))),
% 0.56/0.80      inference('sup-', [status(thm)], ['9', '10'])).
% 0.56/0.80  thf('12', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_D_1))),
% 0.56/0.80      inference('sup-', [status(thm)], ['9', '10'])).
% 0.56/0.80  thf(t64_zfmisc_1, axiom,
% 0.56/0.80    (![A:$i,B:$i,C:$i]:
% 0.56/0.80     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.56/0.80       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.56/0.80  thf('13', plain,
% 0.56/0.80      (![X19 : $i, X20 : $i, X22 : $i]:
% 0.56/0.80         ((r2_hidden @ X19 @ (k4_xboole_0 @ X20 @ (k1_tarski @ X22)))
% 0.56/0.80          | ((X19) = (X22))
% 0.56/0.80          | ~ (r2_hidden @ X19 @ X20))),
% 0.56/0.80      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.56/0.80  thf('14', plain,
% 0.56/0.80      (![X0 : $i]:
% 0.56/0.80         (((k2_mcart_1 @ sk_A) = (X0))
% 0.56/0.80          | (r2_hidden @ (k2_mcart_1 @ sk_A) @ 
% 0.56/0.80             (k4_xboole_0 @ (k1_tarski @ sk_D_1) @ (k1_tarski @ X0))))),
% 0.56/0.80      inference('sup-', [status(thm)], ['12', '13'])).
% 0.56/0.80  thf(d5_xboole_0, axiom,
% 0.56/0.80    (![A:$i,B:$i,C:$i]:
% 0.56/0.80     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.56/0.80       ( ![D:$i]:
% 0.56/0.80         ( ( r2_hidden @ D @ C ) <=>
% 0.56/0.80           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.56/0.80  thf('15', plain,
% 0.56/0.80      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.56/0.80         (~ (r2_hidden @ X4 @ X3)
% 0.56/0.80          | ~ (r2_hidden @ X4 @ X2)
% 0.56/0.80          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.56/0.80      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.56/0.80  thf('16', plain,
% 0.56/0.80      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.56/0.80         (~ (r2_hidden @ X4 @ X2)
% 0.56/0.80          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.56/0.80      inference('simplify', [status(thm)], ['15'])).
% 0.56/0.80  thf('17', plain,
% 0.56/0.80      (![X0 : $i]:
% 0.56/0.80         (((k2_mcart_1 @ sk_A) = (X0))
% 0.56/0.80          | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ X0)))),
% 0.56/0.80      inference('sup-', [status(thm)], ['14', '16'])).
% 0.56/0.80  thf('18', plain, (((k2_mcart_1 @ sk_A) = (sk_D_1))),
% 0.56/0.80      inference('sup-', [status(thm)], ['11', '17'])).
% 0.56/0.80  thf('19', plain,
% 0.56/0.80      ((((k2_mcart_1 @ sk_A) != (sk_D_1)))
% 0.56/0.80         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.56/0.80      inference('split', [status(esa)], ['7'])).
% 0.56/0.80  thf('20', plain,
% 0.56/0.80      ((((sk_D_1) != (sk_D_1))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.56/0.80      inference('sup-', [status(thm)], ['18', '19'])).
% 0.56/0.80  thf('21', plain, ((((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.56/0.80      inference('simplify', [status(thm)], ['20'])).
% 0.56/0.80  thf('22', plain,
% 0.56/0.80      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.56/0.80       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.56/0.80      inference('split', [status(esa)], ['7'])).
% 0.56/0.80  thf('23', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.56/0.80      inference('sat_resolution*', [status(thm)], ['21', '22'])).
% 0.56/0.80  thf('24', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.56/0.80      inference('simpl_trail', [status(thm)], ['8', '23'])).
% 0.56/0.80  thf('25', plain,
% 0.56/0.80      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.56/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.80  thf('26', plain,
% 0.56/0.80      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 0.56/0.80         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.56/0.80      inference('split', [status(esa)], ['25'])).
% 0.56/0.80  thf('27', plain,
% 0.56/0.80      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | 
% 0.56/0.80       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.56/0.80      inference('split', [status(esa)], ['25'])).
% 0.56/0.80  thf('28', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.56/0.80      inference('sat_resolution*', [status(thm)], ['21', '27'])).
% 0.56/0.80  thf('29', plain, (((k1_mcart_1 @ sk_A) != (sk_C))),
% 0.56/0.80      inference('simpl_trail', [status(thm)], ['26', '28'])).
% 0.56/0.80  thf('30', plain, ($false),
% 0.56/0.80      inference('simplify_reflect-', [status(thm)], ['6', '24', '29'])).
% 0.56/0.80  
% 0.56/0.80  % SZS output end Refutation
% 0.56/0.80  
% 0.56/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
