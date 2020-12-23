%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xKcoFbKG6T

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:14 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 130 expanded)
%              Number of leaves         :   27 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  450 (1025 expanded)
%              Number of equality atoms :   26 (  48 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X33 @ X34 ) )
        = ( k9_relat_1 @ X33 @ X34 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t167_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t167_funct_1])).

thf('1',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X26 ) @ X27 )
      | ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_xboole_0 @ X36 @ ( k1_relat_1 @ X37 ) )
      | ( ( k7_relat_1 @ X37 @ X36 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X35: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X35 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('14',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_xboole_0 @ X36 @ ( k1_relat_1 @ X37 ) )
      | ( ( k7_relat_1 @ X37 @ X36 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X33 @ X34 ) )
        = ( k9_relat_1 @ X33 @ X34 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['19','25'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('28',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','26','27'])).

thf('29',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','26','27'])).

thf(t118_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) )
       => ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ) )).

thf('30',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X38 @ ( k1_relat_1 @ X39 ) )
      | ~ ( r2_hidden @ X40 @ ( k1_relat_1 @ X39 ) )
      | ( ( k9_relat_1 @ X39 @ ( k2_tarski @ X38 @ X40 ) )
        = ( k2_tarski @ ( k1_funct_1 @ X39 @ X38 ) @ ( k1_funct_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t118_funct_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ sk_A ) )
    = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('36',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('37',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('38',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['4','38','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xKcoFbKG6T
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:37:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 525 iterations in 0.202s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.66  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.66  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.66  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.66  thf(t148_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ B ) =>
% 0.45/0.66       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.45/0.66  thf('0', plain,
% 0.45/0.66      (![X33 : $i, X34 : $i]:
% 0.45/0.66         (((k2_relat_1 @ (k7_relat_1 @ X33 @ X34)) = (k9_relat_1 @ X33 @ X34))
% 0.45/0.66          | ~ (v1_relat_1 @ X33))),
% 0.45/0.66      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.45/0.66  thf(t167_funct_1, conjecture,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.66       ( r1_tarski @
% 0.45/0.66         ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ 
% 0.45/0.66         ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i,B:$i]:
% 0.45/0.66        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.66          ( r1_tarski @
% 0.45/0.66            ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ 
% 0.45/0.66            ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t167_funct_1])).
% 0.45/0.66  thf('1', plain,
% 0.45/0.66      (~ (r1_tarski @ 
% 0.45/0.66          (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.45/0.66          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      ((~ (r1_tarski @ (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.45/0.66           (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.66  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('4', plain,
% 0.45/0.66      (~ (r1_tarski @ (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.45/0.66          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['2', '3'])).
% 0.45/0.66  thf(l27_zfmisc_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X26 : $i, X27 : $i]:
% 0.45/0.66         ((r1_xboole_0 @ (k1_tarski @ X26) @ X27) | (r2_hidden @ X26 @ X27))),
% 0.45/0.66      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.45/0.66  thf(t187_relat_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.45/0.66           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.45/0.66  thf('6', plain,
% 0.45/0.66      (![X36 : $i, X37 : $i]:
% 0.45/0.66         (~ (r1_xboole_0 @ X36 @ (k1_relat_1 @ X37))
% 0.45/0.66          | ((k7_relat_1 @ X37 @ X36) = (k1_xboole_0))
% 0.45/0.66          | ~ (v1_relat_1 @ X37))),
% 0.45/0.66      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.45/0.66  thf('7', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ((k7_relat_1 @ X0 @ (k1_tarski @ X1)) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.66  thf('8', plain,
% 0.45/0.66      (~ (r1_tarski @ 
% 0.45/0.66          (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.45/0.66          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('9', plain,
% 0.45/0.66      ((~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ 
% 0.45/0.66           (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_B)
% 0.45/0.66        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.66  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      ((~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ 
% 0.45/0.66           (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.45/0.66        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.66  thf(t150_relat_1, axiom,
% 0.45/0.66    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (![X35 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X35) = (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.45/0.66  thf(t79_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.45/0.66  thf('13', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X5)),
% 0.45/0.66      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      (![X36 : $i, X37 : $i]:
% 0.45/0.66         (~ (r1_xboole_0 @ X36 @ (k1_relat_1 @ X37))
% 0.45/0.66          | ((k7_relat_1 @ X37 @ X36) = (k1_xboole_0))
% 0.45/0.66          | ~ (v1_relat_1 @ X37))),
% 0.45/0.66      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.45/0.66  thf('15', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ((k7_relat_1 @ X0 @ (k4_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.45/0.66              = (k1_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.66  thf('16', plain,
% 0.45/0.66      (![X33 : $i, X34 : $i]:
% 0.45/0.66         (((k2_relat_1 @ (k7_relat_1 @ X33 @ X34)) = (k9_relat_1 @ X33 @ X34))
% 0.45/0.66          | ~ (v1_relat_1 @ X33))),
% 0.45/0.66      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k2_relat_1 @ k1_xboole_0)
% 0.45/0.66            = (k9_relat_1 @ X0 @ (k4_xboole_0 @ X1 @ (k1_relat_1 @ X0))))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['15', '16'])).
% 0.45/0.66  thf('18', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ((k2_relat_1 @ k1_xboole_0)
% 0.45/0.66              = (k9_relat_1 @ X0 @ (k4_xboole_0 @ X1 @ (k1_relat_1 @ X0)))))),
% 0.45/0.66      inference('simplify', [status(thm)], ['17'])).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.45/0.66        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['12', '18'])).
% 0.45/0.66  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('21', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ((k7_relat_1 @ X0 @ (k4_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.45/0.66              = (k1_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.66  thf(dt_k7_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      (![X28 : $i, X29 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X28) | (v1_relat_1 @ (k7_relat_1 @ X28 @ X29)))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.45/0.66  thf('23', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((v1_relat_1 @ k1_xboole_0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['21', '22'])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['23'])).
% 0.45/0.66  thf('25', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.45/0.66      inference('sup-', [status(thm)], ['20', '24'])).
% 0.45/0.66  thf('26', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['19', '25'])).
% 0.45/0.66  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.66  thf('27', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.45/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.66  thf('28', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['11', '26', '27'])).
% 0.45/0.66  thf('29', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['11', '26', '27'])).
% 0.45/0.66  thf(t118_funct_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.66       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.45/0.66           ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) ) =>
% 0.45/0.66         ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.45/0.66           ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ))).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X38 @ (k1_relat_1 @ X39))
% 0.45/0.66          | ~ (r2_hidden @ X40 @ (k1_relat_1 @ X39))
% 0.45/0.66          | ((k9_relat_1 @ X39 @ (k2_tarski @ X38 @ X40))
% 0.45/0.66              = (k2_tarski @ (k1_funct_1 @ X39 @ X38) @ 
% 0.45/0.66                 (k1_funct_1 @ X39 @ X40)))
% 0.45/0.66          | ~ (v1_funct_1 @ X39)
% 0.45/0.66          | ~ (v1_relat_1 @ X39))),
% 0.45/0.66      inference('cnf', [status(esa)], [t118_funct_1])).
% 0.45/0.66  thf('31', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ sk_B)
% 0.45/0.66          | ~ (v1_funct_1 @ sk_B)
% 0.45/0.66          | ((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ X0))
% 0.45/0.66              = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.45/0.66                 (k1_funct_1 @ sk_B @ X0)))
% 0.45/0.66          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.66  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('33', plain, ((v1_funct_1 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('34', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ X0))
% 0.45/0.66            = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.45/0.66               (k1_funct_1 @ sk_B @ X0)))
% 0.45/0.66          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.45/0.66  thf('35', plain,
% 0.45/0.66      (((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ sk_A))
% 0.45/0.66         = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['28', '34'])).
% 0.45/0.66  thf(t69_enumset1, axiom,
% 0.45/0.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.66  thf('36', plain,
% 0.45/0.66      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.45/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.66  thf('37', plain,
% 0.45/0.66      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.45/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.66  thf('38', plain,
% 0.45/0.66      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.45/0.66         = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.45/0.66  thf(d10_xboole_0, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.66  thf('39', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.45/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.66  thf('40', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.66      inference('simplify', [status(thm)], ['39'])).
% 0.45/0.66  thf('41', plain, ($false),
% 0.45/0.66      inference('demod', [status(thm)], ['4', '38', '40'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
