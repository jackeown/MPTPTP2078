%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GNuI8YtkiC

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  69 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :  312 ( 545 expanded)
%              Number of equality atoms :   23 (  32 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('0',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k10_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( sk_D @ X13 @ X11 @ X12 ) ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( sk_D @ X1 @ X0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('9',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('16',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X2 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k10_relat_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','21'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GNuI8YtkiC
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.59  % Solved by: fo/fo7.sh
% 0.20/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.59  % done 189 iterations in 0.138s
% 0.20/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.59  % SZS output start Refutation
% 0.20/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.59  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.59  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.59  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.20/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.59  thf(t172_relat_1, conjecture,
% 0.20/0.59    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.59    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.20/0.59    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.20/0.59  thf('0', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(cc1_relat_1, axiom,
% 0.20/0.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.20/0.59  thf('1', plain, (![X9 : $i]: ((v1_relat_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.20/0.59      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.59  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.59  thf('2', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.20/0.59      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.59  thf(t3_xboole_0, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.59            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.59  thf('3', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.59  thf(t166_relat_1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( v1_relat_1 @ C ) =>
% 0.20/0.59       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.20/0.59         ( ?[D:$i]:
% 0.20/0.59           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.59             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.20/0.59             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.59  thf('4', plain,
% 0.20/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X12 @ (k10_relat_1 @ X13 @ X11))
% 0.20/0.59          | (r2_hidden @ (k4_tarski @ X12 @ (sk_D @ X13 @ X11 @ X12)) @ X13)
% 0.20/0.59          | ~ (v1_relat_1 @ X13))),
% 0.20/0.59      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.59  thf('5', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.59         ((r1_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.59          | ~ (v1_relat_1 @ X1)
% 0.20/0.59          | (r2_hidden @ 
% 0.20/0.59             (k4_tarski @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.20/0.59              (sk_D @ X1 @ X0 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0)))) @ 
% 0.20/0.59             X1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.59  thf(t7_tarski, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ~( ( r2_hidden @ A @ B ) & 
% 0.20/0.59          ( ![C:$i]:
% 0.20/0.59            ( ~( ( r2_hidden @ C @ B ) & 
% 0.20/0.59                 ( ![D:$i]:
% 0.20/0.59                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.59  thf('6', plain,
% 0.20/0.59      (![X6 : $i, X7 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X6 @ X7) | (r2_hidden @ (sk_C_1 @ X7) @ X7))),
% 0.20/0.59      inference('cnf', [status(esa)], [t7_tarski])).
% 0.20/0.59  thf('7', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.59         (~ (v1_relat_1 @ X0)
% 0.20/0.59          | (r1_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ X2)
% 0.20/0.59          | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.59  thf(t7_xboole_0, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.59          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.59  thf('8', plain,
% 0.20/0.59      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.20/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.59  thf('9', plain,
% 0.20/0.59      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.20/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.59  thf('10', plain,
% 0.20/0.59      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X2 @ X0)
% 0.20/0.59          | ~ (r2_hidden @ X2 @ X3)
% 0.20/0.59          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.59  thf('11', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (((X0) = (k1_xboole_0))
% 0.20/0.59          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.59          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.59  thf('12', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (((X0) = (k1_xboole_0))
% 0.20/0.59          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.20/0.59          | ((X0) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.59  thf('13', plain,
% 0.20/0.59      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.59      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.59  thf('14', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((r2_hidden @ (sk_C_1 @ X1) @ X1)
% 0.20/0.59          | ~ (v1_relat_1 @ X1)
% 0.20/0.59          | ((k10_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['7', '13'])).
% 0.20/0.59  thf('15', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((r2_hidden @ (sk_C_1 @ X1) @ X1)
% 0.20/0.59          | ~ (v1_relat_1 @ X1)
% 0.20/0.59          | ((k10_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['7', '13'])).
% 0.20/0.59  thf('16', plain,
% 0.20/0.59      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X2 @ X0)
% 0.20/0.59          | ~ (r2_hidden @ X2 @ X3)
% 0.20/0.59          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.59  thf('17', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.59         (((k10_relat_1 @ X0 @ X2) = (k1_xboole_0))
% 0.20/0.59          | ~ (v1_relat_1 @ X0)
% 0.20/0.59          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.59          | ~ (r2_hidden @ (sk_C_1 @ X0) @ X1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.59  thf('18', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.59         (((k10_relat_1 @ X0 @ X2) = (k1_xboole_0))
% 0.20/0.59          | ~ (v1_relat_1 @ X0)
% 0.20/0.59          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.20/0.59          | ~ (v1_relat_1 @ X0)
% 0.20/0.59          | ((k10_relat_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['14', '17'])).
% 0.20/0.59  thf('19', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.59         (((k10_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.20/0.59          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.20/0.59          | ~ (v1_relat_1 @ X0)
% 0.20/0.59          | ((k10_relat_1 @ X0 @ X2) = (k1_xboole_0)))),
% 0.20/0.59      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.59  thf('20', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.20/0.59          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.59          | ((k10_relat_1 @ k1_xboole_0 @ X1) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['2', '19'])).
% 0.20/0.59  thf('21', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.20/0.59          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.59      inference('condensation', [status(thm)], ['20'])).
% 0.20/0.59  thf('22', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.59          | ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['1', '21'])).
% 0.20/0.59  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.59  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.59  thf('24', plain,
% 0.20/0.59      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.59      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.59  thf('25', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.59      inference('demod', [status(thm)], ['0', '24'])).
% 0.20/0.59  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 0.20/0.59  
% 0.20/0.59  % SZS output end Refutation
% 0.20/0.59  
% 0.20/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
