%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.414JiopBRm

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:42 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   52 (  64 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :  334 ( 487 expanded)
%              Number of equality atoms :   21 (  32 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_tarski_type,type,(
    r2_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t136_zfmisc_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ~ ( ( r1_tarski @ C @ B )
            & ~ ( r2_tarski @ C @ B )
            & ~ ( r2_hidden @ C @ B ) )
      & ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ ( k1_zfmisc_1 @ C ) @ B ) )
      & ! [C: $i,D: $i] :
          ( ( ( r2_hidden @ C @ B )
            & ( r1_tarski @ D @ C ) )
         => ( r2_hidden @ D @ B ) )
      & ( r2_hidden @ A @ B ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( sk_B @ X18 ) ) ),
    inference(cnf,[status(esa)],[t136_zfmisc_1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X28: $i] :
      ( ( r2_hidden @ X25 @ ( k4_xboole_0 @ X26 @ ( k1_tarski @ X28 ) ) )
      | ( X25 = X28 )
      | ~ ( r2_hidden @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( sk_B @ X0 ) @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t140_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ X23 @ ( k1_tarski @ X24 ) ) @ ( k1_tarski @ X24 ) )
        = X23 )
      | ~ ( r2_hidden @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t140_zfmisc_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X24 ) @ ( k4_xboole_0 @ X23 @ ( k1_tarski @ X24 ) ) )
        = X23 )
      | ~ ( r2_hidden @ X24 @ X23 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( sk_B @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X1 ) ) )
        = ( k4_xboole_0 @ ( sk_B @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t12_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
       => ( ( ( k1_mcart_1 @ A )
            = B )
          & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_mcart_1])).

thf('7',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('8',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X29 ) @ X30 )
      | ~ ( r2_hidden @ X29 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('9',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k4_xboole_0 @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ X0 ) ) )
      | ( sk_B_1 = X0 ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25 != X27 )
      | ~ ( r2_hidden @ X25 @ ( k4_xboole_0 @ X26 @ ( k1_tarski @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('16',plain,(
    ! [X26: $i,X27: $i] :
      ~ ( r2_hidden @ X27 @ ( k4_xboole_0 @ X26 @ ( k1_tarski @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( sk_B_1
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B_1 )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B_1 )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B_1 ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X29 ) @ X31 )
      | ~ ( r2_hidden @ X29 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('22',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['18'])).

thf('24',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B_1 )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['18'])).

thf('26',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['24','25'])).

thf('27',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B_1 ),
    inference(simpl_trail,[status(thm)],['19','26'])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.414JiopBRm
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.46/1.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.46/1.68  % Solved by: fo/fo7.sh
% 1.46/1.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.46/1.68  % done 1995 iterations in 1.224s
% 1.46/1.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.46/1.68  % SZS output start Refutation
% 1.46/1.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.46/1.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.46/1.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.46/1.68  thf(sk_B_type, type, sk_B: $i > $i).
% 1.46/1.68  thf(sk_A_type, type, sk_A: $i).
% 1.46/1.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.46/1.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.46/1.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.46/1.68  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.46/1.68  thf(r2_tarski_type, type, r2_tarski: $i > $i > $o).
% 1.46/1.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.46/1.68  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.46/1.68  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.46/1.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.46/1.68  thf(t136_zfmisc_1, axiom,
% 1.46/1.68    (![A:$i]:
% 1.46/1.68     ( ?[B:$i]:
% 1.46/1.68       ( ( ![C:$i]:
% 1.46/1.68           ( ~( ( r1_tarski @ C @ B ) & ( ~( r2_tarski @ C @ B ) ) & 
% 1.46/1.68                ( ~( r2_hidden @ C @ B ) ) ) ) ) & 
% 1.46/1.68         ( ![C:$i]:
% 1.46/1.68           ( ( r2_hidden @ C @ B ) => ( r2_hidden @ ( k1_zfmisc_1 @ C ) @ B ) ) ) & 
% 1.46/1.68         ( ![C:$i,D:$i]:
% 1.46/1.68           ( ( ( r2_hidden @ C @ B ) & ( r1_tarski @ D @ C ) ) =>
% 1.46/1.68             ( r2_hidden @ D @ B ) ) ) & 
% 1.46/1.68         ( r2_hidden @ A @ B ) ) ))).
% 1.46/1.68  thf('0', plain, (![X18 : $i]: (r2_hidden @ X18 @ (sk_B @ X18))),
% 1.46/1.68      inference('cnf', [status(esa)], [t136_zfmisc_1])).
% 1.46/1.68  thf(t64_zfmisc_1, axiom,
% 1.46/1.68    (![A:$i,B:$i,C:$i]:
% 1.46/1.68     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 1.46/1.68       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 1.46/1.68  thf('1', plain,
% 1.46/1.68      (![X25 : $i, X26 : $i, X28 : $i]:
% 1.46/1.68         ((r2_hidden @ X25 @ (k4_xboole_0 @ X26 @ (k1_tarski @ X28)))
% 1.46/1.68          | ((X25) = (X28))
% 1.46/1.68          | ~ (r2_hidden @ X25 @ X26))),
% 1.46/1.68      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 1.46/1.68  thf('2', plain,
% 1.46/1.68      (![X0 : $i, X1 : $i]:
% 1.46/1.68         (((X0) = (X1))
% 1.46/1.68          | (r2_hidden @ X0 @ (k4_xboole_0 @ (sk_B @ X0) @ (k1_tarski @ X1))))),
% 1.46/1.68      inference('sup-', [status(thm)], ['0', '1'])).
% 1.46/1.68  thf(t140_zfmisc_1, axiom,
% 1.46/1.68    (![A:$i,B:$i]:
% 1.46/1.68     ( ( r2_hidden @ A @ B ) =>
% 1.46/1.68       ( ( k2_xboole_0 @
% 1.46/1.68           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 1.46/1.68         ( B ) ) ))).
% 1.46/1.68  thf('3', plain,
% 1.46/1.68      (![X23 : $i, X24 : $i]:
% 1.46/1.68         (((k2_xboole_0 @ (k4_xboole_0 @ X23 @ (k1_tarski @ X24)) @ 
% 1.46/1.68            (k1_tarski @ X24)) = (X23))
% 1.46/1.68          | ~ (r2_hidden @ X24 @ X23))),
% 1.46/1.68      inference('cnf', [status(esa)], [t140_zfmisc_1])).
% 1.46/1.68  thf(commutativity_k2_xboole_0, axiom,
% 1.46/1.68    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.46/1.68  thf('4', plain,
% 1.46/1.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.46/1.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.46/1.68  thf('5', plain,
% 1.46/1.68      (![X23 : $i, X24 : $i]:
% 1.46/1.68         (((k2_xboole_0 @ (k1_tarski @ X24) @ 
% 1.46/1.68            (k4_xboole_0 @ X23 @ (k1_tarski @ X24))) = (X23))
% 1.46/1.68          | ~ (r2_hidden @ X24 @ X23))),
% 1.46/1.68      inference('demod', [status(thm)], ['3', '4'])).
% 1.46/1.68  thf('6', plain,
% 1.46/1.68      (![X0 : $i, X1 : $i]:
% 1.46/1.68         (((X1) = (X0))
% 1.46/1.68          | ((k2_xboole_0 @ (k1_tarski @ X1) @ 
% 1.46/1.68              (k4_xboole_0 @ (k4_xboole_0 @ (sk_B @ X1) @ (k1_tarski @ X0)) @ 
% 1.46/1.68               (k1_tarski @ X1)))
% 1.46/1.68              = (k4_xboole_0 @ (sk_B @ X1) @ (k1_tarski @ X0))))),
% 1.46/1.68      inference('sup-', [status(thm)], ['2', '5'])).
% 1.46/1.68  thf(t12_mcart_1, conjecture,
% 1.46/1.68    (![A:$i,B:$i,C:$i]:
% 1.46/1.68     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 1.46/1.68       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 1.46/1.68         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.46/1.68  thf(zf_stmt_0, negated_conjecture,
% 1.46/1.68    (~( ![A:$i,B:$i,C:$i]:
% 1.46/1.68        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 1.46/1.68          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 1.46/1.68            ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )),
% 1.46/1.68    inference('cnf.neg', [status(esa)], [t12_mcart_1])).
% 1.46/1.68  thf('7', plain,
% 1.46/1.68      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_C_1))),
% 1.46/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.68  thf(t10_mcart_1, axiom,
% 1.46/1.68    (![A:$i,B:$i,C:$i]:
% 1.46/1.68     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 1.46/1.68       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.46/1.68         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.46/1.68  thf('8', plain,
% 1.46/1.68      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.46/1.68         ((r2_hidden @ (k1_mcart_1 @ X29) @ X30)
% 1.46/1.68          | ~ (r2_hidden @ X29 @ (k2_zfmisc_1 @ X30 @ X31)))),
% 1.46/1.68      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.46/1.68  thf('9', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B_1))),
% 1.46/1.68      inference('sup-', [status(thm)], ['7', '8'])).
% 1.46/1.68  thf(t7_xboole_1, axiom,
% 1.46/1.68    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.46/1.68  thf('10', plain,
% 1.46/1.68      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 1.46/1.68      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.46/1.68  thf(d3_tarski, axiom,
% 1.46/1.68    (![A:$i,B:$i]:
% 1.46/1.68     ( ( r1_tarski @ A @ B ) <=>
% 1.46/1.68       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.46/1.68  thf('11', plain,
% 1.46/1.68      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.46/1.68         (~ (r2_hidden @ X2 @ X3)
% 1.46/1.68          | (r2_hidden @ X2 @ X4)
% 1.46/1.68          | ~ (r1_tarski @ X3 @ X4))),
% 1.46/1.68      inference('cnf', [status(esa)], [d3_tarski])).
% 1.46/1.68  thf('12', plain,
% 1.46/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.68         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 1.46/1.68      inference('sup-', [status(thm)], ['10', '11'])).
% 1.46/1.68  thf('13', plain,
% 1.46/1.68      (![X0 : $i]:
% 1.46/1.68         (r2_hidden @ (k1_mcart_1 @ sk_A) @ 
% 1.46/1.68          (k2_xboole_0 @ (k1_tarski @ sk_B_1) @ X0))),
% 1.46/1.68      inference('sup-', [status(thm)], ['9', '12'])).
% 1.46/1.68  thf('14', plain,
% 1.46/1.68      (![X0 : $i]:
% 1.46/1.68         ((r2_hidden @ (k1_mcart_1 @ sk_A) @ 
% 1.46/1.68           (k4_xboole_0 @ (sk_B @ sk_B_1) @ (k1_tarski @ X0)))
% 1.46/1.68          | ((sk_B_1) = (X0)))),
% 1.46/1.68      inference('sup+', [status(thm)], ['6', '13'])).
% 1.46/1.68  thf('15', plain,
% 1.46/1.68      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.46/1.68         (((X25) != (X27))
% 1.46/1.68          | ~ (r2_hidden @ X25 @ (k4_xboole_0 @ X26 @ (k1_tarski @ X27))))),
% 1.46/1.68      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 1.46/1.68  thf('16', plain,
% 1.46/1.68      (![X26 : $i, X27 : $i]:
% 1.46/1.68         ~ (r2_hidden @ X27 @ (k4_xboole_0 @ X26 @ (k1_tarski @ X27)))),
% 1.46/1.68      inference('simplify', [status(thm)], ['15'])).
% 1.46/1.68  thf('17', plain, (((sk_B_1) = (k1_mcart_1 @ sk_A))),
% 1.46/1.68      inference('sup-', [status(thm)], ['14', '16'])).
% 1.46/1.68  thf('18', plain,
% 1.46/1.68      ((((k1_mcart_1 @ sk_A) != (sk_B_1))
% 1.46/1.68        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))),
% 1.46/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.68  thf('19', plain,
% 1.46/1.68      ((((k1_mcart_1 @ sk_A) != (sk_B_1)))
% 1.46/1.68         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B_1))))),
% 1.46/1.68      inference('split', [status(esa)], ['18'])).
% 1.46/1.68  thf('20', plain,
% 1.46/1.68      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_C_1))),
% 1.46/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.68  thf('21', plain,
% 1.46/1.68      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.46/1.68         ((r2_hidden @ (k2_mcart_1 @ X29) @ X31)
% 1.46/1.68          | ~ (r2_hidden @ X29 @ (k2_zfmisc_1 @ X30 @ X31)))),
% 1.46/1.68      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.46/1.68  thf('22', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1)),
% 1.46/1.68      inference('sup-', [status(thm)], ['20', '21'])).
% 1.46/1.68  thf('23', plain,
% 1.46/1.68      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))
% 1.46/1.68         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1)))),
% 1.46/1.68      inference('split', [status(esa)], ['18'])).
% 1.46/1.68  thf('24', plain, (((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))),
% 1.46/1.68      inference('sup-', [status(thm)], ['22', '23'])).
% 1.46/1.68  thf('25', plain,
% 1.46/1.68      (~ (((k1_mcart_1 @ sk_A) = (sk_B_1))) | 
% 1.46/1.68       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))),
% 1.46/1.68      inference('split', [status(esa)], ['18'])).
% 1.46/1.68  thf('26', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B_1)))),
% 1.46/1.68      inference('sat_resolution*', [status(thm)], ['24', '25'])).
% 1.46/1.68  thf('27', plain, (((k1_mcart_1 @ sk_A) != (sk_B_1))),
% 1.46/1.68      inference('simpl_trail', [status(thm)], ['19', '26'])).
% 1.46/1.68  thf('28', plain, ($false),
% 1.46/1.68      inference('simplify_reflect-', [status(thm)], ['17', '27'])).
% 1.46/1.68  
% 1.46/1.68  % SZS output end Refutation
% 1.46/1.68  
% 1.46/1.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
