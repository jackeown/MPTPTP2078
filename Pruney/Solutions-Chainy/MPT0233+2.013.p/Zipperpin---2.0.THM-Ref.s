%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jumpuRp0zC

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:39 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   48 (  54 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  313 ( 387 expanded)
%              Number of equality atoms :   32 (  44 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X27 != X26 )
      | ( r2_hidden @ X27 @ X28 )
      | ( X28
       != ( k2_tarski @ X29 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X26: $i,X29: $i] :
      ( r2_hidden @ X26 @ ( k2_tarski @ X29 @ X26 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X64: $i,X65: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X64 ) @ X65 )
      | ( r2_hidden @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('5',plain,(
    ! [X66: $i,X68: $i,X69: $i] :
      ( ( r1_tarski @ X68 @ ( k2_tarski @ X66 @ X69 ) )
      | ( X68
       != ( k1_tarski @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('6',plain,(
    ! [X66: $i,X69: $i] :
      ( r1_tarski @ ( k1_tarski @ X66 ) @ ( k2_tarski @ X66 @ X69 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('7',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_2 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_2 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k2_tarski @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B_2 ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','18'])).

thf('20',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['3','19'])).

thf('21',plain,(
    ! [X26: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X28 )
      | ( X30 = X29 )
      | ( X30 = X26 )
      | ( X28
       != ( k2_tarski @ X29 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('22',plain,(
    ! [X26: $i,X29: $i,X30: $i] :
      ( ( X30 = X26 )
      | ( X30 = X29 )
      | ~ ( r2_hidden @ X30 @ ( k2_tarski @ X29 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jumpuRp0zC
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:02:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 211 iterations in 0.147s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.42/0.60  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.42/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.60  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.42/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.60  thf(t69_enumset1, axiom,
% 0.42/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.42/0.60  thf('0', plain, (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.42/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.60  thf(d2_tarski, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.42/0.60       ( ![D:$i]:
% 0.42/0.60         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.42/0.60         (((X27) != (X26))
% 0.42/0.60          | (r2_hidden @ X27 @ X28)
% 0.42/0.60          | ((X28) != (k2_tarski @ X29 @ X26)))),
% 0.42/0.60      inference('cnf', [status(esa)], [d2_tarski])).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      (![X26 : $i, X29 : $i]: (r2_hidden @ X26 @ (k2_tarski @ X29 @ X26))),
% 0.42/0.60      inference('simplify', [status(thm)], ['1'])).
% 0.42/0.60  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['0', '2'])).
% 0.42/0.60  thf(l27_zfmisc_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.42/0.60  thf('4', plain,
% 0.42/0.60      (![X64 : $i, X65 : $i]:
% 0.42/0.60         ((r1_xboole_0 @ (k1_tarski @ X64) @ X65) | (r2_hidden @ X64 @ X65))),
% 0.42/0.60      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.42/0.60  thf(l45_zfmisc_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.42/0.60       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.42/0.60            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.42/0.60  thf('5', plain,
% 0.42/0.60      (![X66 : $i, X68 : $i, X69 : $i]:
% 0.42/0.60         ((r1_tarski @ X68 @ (k2_tarski @ X66 @ X69))
% 0.42/0.60          | ((X68) != (k1_tarski @ X66)))),
% 0.42/0.60      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.42/0.60  thf('6', plain,
% 0.42/0.60      (![X66 : $i, X69 : $i]:
% 0.42/0.60         (r1_tarski @ (k1_tarski @ X66) @ (k2_tarski @ X66 @ X69))),
% 0.42/0.60      inference('simplify', [status(thm)], ['5'])).
% 0.42/0.60  thf(t28_zfmisc_1, conjecture,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.42/0.60          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.42/0.60             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_2) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(t28_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.42/0.60  thf('8', plain,
% 0.42/0.60      (![X18 : $i, X19 : $i]:
% 0.42/0.60         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.42/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.42/0.60  thf('9', plain,
% 0.42/0.60      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B_2) @ 
% 0.42/0.60         (k2_tarski @ sk_C_1 @ sk_D_1)) = (k2_tarski @ sk_A @ sk_B_2))),
% 0.42/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.42/0.60  thf(commutativity_k3_xboole_0, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.42/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.42/0.60  thf(t18_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.60         ((r1_tarski @ X15 @ X16)
% 0.42/0.60          | ~ (r1_tarski @ X15 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.42/0.60  thf('12', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B_2))
% 0.42/0.60          | (r1_tarski @ X0 @ (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['9', '12'])).
% 0.42/0.60  thf('14', plain,
% 0.42/0.60      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['6', '13'])).
% 0.42/0.60  thf('15', plain,
% 0.42/0.60      (![X18 : $i, X19 : $i]:
% 0.42/0.60         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.42/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.42/0.60  thf('16', plain,
% 0.42/0.60      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))
% 0.42/0.60         = (k1_tarski @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.42/0.60  thf(t4_xboole_0, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.42/0.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.42/0.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.42/0.60            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.42/0.60  thf('17', plain,
% 0.42/0.60      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.42/0.60          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.42/0.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.42/0.60  thf('18', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.42/0.60          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.60  thf('19', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D_1))
% 0.42/0.60          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['4', '18'])).
% 0.42/0.60  thf('20', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['3', '19'])).
% 0.42/0.60  thf('21', plain,
% 0.42/0.60      (![X26 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X30 @ X28)
% 0.42/0.60          | ((X30) = (X29))
% 0.42/0.60          | ((X30) = (X26))
% 0.42/0.60          | ((X28) != (k2_tarski @ X29 @ X26)))),
% 0.42/0.60      inference('cnf', [status(esa)], [d2_tarski])).
% 0.42/0.60  thf('22', plain,
% 0.42/0.60      (![X26 : $i, X29 : $i, X30 : $i]:
% 0.42/0.60         (((X30) = (X26))
% 0.42/0.60          | ((X30) = (X29))
% 0.42/0.60          | ~ (r2_hidden @ X30 @ (k2_tarski @ X29 @ X26)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['21'])).
% 0.42/0.60  thf('23', plain, ((((sk_A) = (sk_C_1)) | ((sk_A) = (sk_D_1)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['20', '22'])).
% 0.42/0.60  thf('24', plain, (((sk_A) != (sk_D_1))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('25', plain, (((sk_A) != (sk_C_1))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('26', plain, ($false),
% 0.42/0.60      inference('simplify_reflect-', [status(thm)], ['23', '24', '25'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
