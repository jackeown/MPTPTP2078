%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.365MkD1BR8

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  57 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  250 ( 305 expanded)
%              Number of equality atoms :   25 (  32 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t111_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k7_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t111_relat_1])).

thf('0',plain,(
    ( k7_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t96_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k7_relat_1 @ X36 @ X37 )
        = ( k3_xboole_0 @ X36 @ ( k2_zfmisc_1 @ X37 @ ( k2_relat_1 @ X36 ) ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t96_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k7_relat_1 @ X36 @ X37 )
        = ( k1_setfam_1 @ ( k2_tarski @ X36 @ ( k2_zfmisc_1 @ X37 @ ( k2_relat_1 @ X36 ) ) ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('10',plain,(
    ! [X33: $i] :
      ( ( v1_relat_1 @ X33 )
      | ( r2_hidden @ ( sk_B @ X33 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('17',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X3 ) ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('19',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','22'])).

thf('24',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.365MkD1BR8
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:33:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 36 iterations in 0.023s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(t111_relat_1, conjecture,
% 0.20/0.48    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t111_relat_1])).
% 0.20/0.48  thf('0', plain, (((k7_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t96_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( k7_relat_1 @ B @ A ) =
% 0.20/0.48         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X36 : $i, X37 : $i]:
% 0.20/0.48         (((k7_relat_1 @ X36 @ X37)
% 0.20/0.48            = (k3_xboole_0 @ X36 @ (k2_zfmisc_1 @ X37 @ (k2_relat_1 @ X36))))
% 0.20/0.48          | ~ (v1_relat_1 @ X36))),
% 0.20/0.48      inference('cnf', [status(esa)], [t96_relat_1])).
% 0.20/0.48  thf(t12_setfam_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X29 : $i, X30 : $i]:
% 0.20/0.48         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X36 : $i, X37 : $i]:
% 0.20/0.48         (((k7_relat_1 @ X36 @ X37)
% 0.20/0.48            = (k1_setfam_1 @ 
% 0.20/0.48               (k2_tarski @ X36 @ (k2_zfmisc_1 @ X37 @ (k2_relat_1 @ X36)))))
% 0.20/0.48          | ~ (v1_relat_1 @ X36))),
% 0.20/0.48      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf(t48_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.20/0.48           = (k3_xboole_0 @ X5 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X29 : $i, X30 : $i]:
% 0.20/0.48         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.20/0.48           = (k1_setfam_1 @ (k2_tarski @ X5 @ X6)))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf(t4_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X7 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['3', '8'])).
% 0.20/0.48  thf(d1_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) <=>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.48              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X33 : $i]: ((v1_relat_1 @ X33) | (r2_hidden @ (sk_B @ X33) @ X33))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.20/0.48  thf(t3_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.48  thf('11', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.48  thf('12', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.20/0.48           = (k1_setfam_1 @ (k2_tarski @ X5 @ X6)))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X0 @ X0)
% 0.20/0.48           = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf(t4_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.48            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.20/0.48          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X29 : $i, X30 : $i]:
% 0.20/0.48         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X3)))
% 0.20/0.48          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.20/0.48          | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '17'])).
% 0.20/0.48  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.48  thf('19', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.20/0.48      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '20'])).
% 0.20/0.48  thf('22', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['9', '22'])).
% 0.20/0.48  thf('24', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '23'])).
% 0.20/0.48  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
