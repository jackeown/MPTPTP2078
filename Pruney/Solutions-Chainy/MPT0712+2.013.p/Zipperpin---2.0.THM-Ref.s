%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IpR4sJaUqw

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:15 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 117 expanded)
%              Number of leaves         :   27 (  46 expanded)
%              Depth                    :   16
%              Number of atoms          :  514 (1033 expanded)
%              Number of equality atoms :   28 (  50 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) )
        = ( k9_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( r1_xboole_0 @ ( k2_tarski @ X10 @ X12 ) @ X11 )
      | ( r2_hidden @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X19 @ X17 ) @ X18 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ ( k1_tarski @ X1 ) ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('14',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ( ( k7_relat_1 @ X23 @ X24 )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X21 ) ) )
      | ( r2_hidden @ X20 @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('24',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf(t118_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) )
       => ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) )
      | ~ ( r2_hidden @ X27 @ ( k1_relat_1 @ X26 ) )
      | ( ( k9_relat_1 @ X26 @ ( k2_tarski @ X25 @ X27 ) )
        = ( k2_tarski @ ( k1_funct_1 @ X26 @ X25 ) @ ( k1_funct_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t118_funct_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ sk_A ) )
    = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('36',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('37',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['4','37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IpR4sJaUqw
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:16:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 197 iterations in 0.222s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.67  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.67  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.46/0.67  thf(t148_relat_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ B ) =>
% 0.46/0.67       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.46/0.67  thf('0', plain,
% 0.46/0.67      (![X15 : $i, X16 : $i]:
% 0.46/0.67         (((k2_relat_1 @ (k7_relat_1 @ X15 @ X16)) = (k9_relat_1 @ X15 @ X16))
% 0.46/0.67          | ~ (v1_relat_1 @ X15))),
% 0.46/0.67      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.46/0.67  thf(t167_funct_1, conjecture,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.67       ( r1_tarski @
% 0.46/0.67         ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ 
% 0.46/0.67         ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i,B:$i]:
% 0.46/0.67        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.67          ( r1_tarski @
% 0.46/0.67            ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ 
% 0.46/0.67            ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t167_funct_1])).
% 0.46/0.67  thf('1', plain,
% 0.46/0.67      (~ (r1_tarski @ 
% 0.46/0.67          (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.46/0.67          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('2', plain,
% 0.46/0.67      ((~ (r1_tarski @ (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.67           (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.46/0.67        | ~ (v1_relat_1 @ sk_B))),
% 0.46/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.67  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('4', plain,
% 0.46/0.67      (~ (r1_tarski @ (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.67          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.46/0.67      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.67  thf(dt_k7_relat_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.46/0.67  thf('5', plain,
% 0.46/0.67      (![X13 : $i, X14 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X13) | (v1_relat_1 @ (k7_relat_1 @ X13 @ X14)))),
% 0.46/0.67      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.46/0.67  thf(t69_enumset1, axiom,
% 0.46/0.67    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.67  thf('6', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.46/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.67  thf(t57_zfmisc_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.46/0.67          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 0.46/0.67  thf('7', plain,
% 0.46/0.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.67         ((r2_hidden @ X10 @ X11)
% 0.46/0.67          | (r1_xboole_0 @ (k2_tarski @ X10 @ X12) @ X11)
% 0.46/0.67          | (r2_hidden @ X12 @ X11))),
% 0.46/0.67      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 0.46/0.67  thf('8', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.46/0.67          | (r2_hidden @ X0 @ X1)
% 0.46/0.67          | (r2_hidden @ X0 @ X1))),
% 0.46/0.67      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.67  thf('9', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((r2_hidden @ X0 @ X1) | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.46/0.67      inference('simplify', [status(thm)], ['8'])).
% 0.46/0.67  thf(t207_relat_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ C ) =>
% 0.46/0.67       ( ( r1_xboole_0 @ A @ B ) =>
% 0.46/0.67         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.67  thf('10', plain,
% 0.46/0.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.67         (~ (r1_xboole_0 @ X17 @ X18)
% 0.46/0.67          | ~ (v1_relat_1 @ X19)
% 0.46/0.67          | ((k7_relat_1 @ (k7_relat_1 @ X19 @ X17) @ X18) = (k1_xboole_0)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.46/0.67  thf('11', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.67         ((r2_hidden @ X1 @ X0)
% 0.46/0.67          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ (k1_tarski @ X1)) @ X0)
% 0.46/0.67              = (k1_xboole_0))
% 0.46/0.67          | ~ (v1_relat_1 @ X2))),
% 0.46/0.67      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.67  thf(d10_xboole_0, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.67  thf('12', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.67  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.67      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.67  thf(t97_relat_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ B ) =>
% 0.46/0.67       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.46/0.67         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.46/0.67  thf('14', plain,
% 0.46/0.67      (![X23 : $i, X24 : $i]:
% 0.46/0.67         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 0.46/0.67          | ((k7_relat_1 @ X23 @ X24) = (X23))
% 0.46/0.67          | ~ (v1_relat_1 @ X23))),
% 0.46/0.67      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.46/0.67  thf('15', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.67  thf('16', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (((k1_xboole_0) = (k7_relat_1 @ X1 @ (k1_tarski @ X0)))
% 0.46/0.67          | ~ (v1_relat_1 @ X1)
% 0.46/0.67          | (r2_hidden @ X0 @ 
% 0.46/0.67             (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_tarski @ X0))))
% 0.46/0.67          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ (k1_tarski @ X0))))),
% 0.46/0.67      inference('sup+', [status(thm)], ['11', '15'])).
% 0.46/0.67  thf('17', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X1)
% 0.46/0.67          | (r2_hidden @ X0 @ 
% 0.46/0.67             (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_tarski @ X0))))
% 0.46/0.67          | ~ (v1_relat_1 @ X1)
% 0.46/0.67          | ((k1_xboole_0) = (k7_relat_1 @ X1 @ (k1_tarski @ X0))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['5', '16'])).
% 0.46/0.67  thf('18', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (((k1_xboole_0) = (k7_relat_1 @ X1 @ (k1_tarski @ X0)))
% 0.46/0.67          | (r2_hidden @ X0 @ 
% 0.46/0.67             (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_tarski @ X0))))
% 0.46/0.67          | ~ (v1_relat_1 @ X1))),
% 0.46/0.67      inference('simplify', [status(thm)], ['17'])).
% 0.46/0.67  thf(t86_relat_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ C ) =>
% 0.46/0.67       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.46/0.67         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.46/0.67  thf('19', plain,
% 0.46/0.67      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X20 @ (k1_relat_1 @ (k7_relat_1 @ X22 @ X21)))
% 0.46/0.67          | (r2_hidden @ X20 @ (k1_relat_1 @ X22))
% 0.46/0.67          | ~ (v1_relat_1 @ X22))),
% 0.46/0.67      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.46/0.67  thf('20', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X1)
% 0.46/0.67          | ((k1_xboole_0) = (k7_relat_1 @ X1 @ (k1_tarski @ X0)))
% 0.46/0.67          | ~ (v1_relat_1 @ X1)
% 0.46/0.67          | (r2_hidden @ X0 @ (k1_relat_1 @ X1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.67  thf('21', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((r2_hidden @ X0 @ (k1_relat_1 @ X1))
% 0.46/0.67          | ((k1_xboole_0) = (k7_relat_1 @ X1 @ (k1_tarski @ X0)))
% 0.46/0.67          | ~ (v1_relat_1 @ X1))),
% 0.46/0.67      inference('simplify', [status(thm)], ['20'])).
% 0.46/0.67  thf('22', plain,
% 0.46/0.67      (~ (r1_tarski @ 
% 0.46/0.67          (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.46/0.67          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('23', plain,
% 0.46/0.67      ((~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ 
% 0.46/0.67           (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.46/0.67        | ~ (v1_relat_1 @ sk_B)
% 0.46/0.67        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.67  thf(t60_relat_1, axiom,
% 0.46/0.67    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.46/0.67     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.67  thf('24', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.46/0.67  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.67  thf('25', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.46/0.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.67  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('27', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.46/0.67      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.46/0.67  thf('28', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.46/0.67      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.46/0.67  thf(t118_funct_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.67       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.46/0.67           ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) ) =>
% 0.46/0.67         ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.46/0.67           ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ))).
% 0.46/0.67  thf('29', plain,
% 0.46/0.67      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X25 @ (k1_relat_1 @ X26))
% 0.46/0.67          | ~ (r2_hidden @ X27 @ (k1_relat_1 @ X26))
% 0.46/0.67          | ((k9_relat_1 @ X26 @ (k2_tarski @ X25 @ X27))
% 0.46/0.67              = (k2_tarski @ (k1_funct_1 @ X26 @ X25) @ 
% 0.46/0.67                 (k1_funct_1 @ X26 @ X27)))
% 0.46/0.67          | ~ (v1_funct_1 @ X26)
% 0.46/0.67          | ~ (v1_relat_1 @ X26))),
% 0.46/0.67      inference('cnf', [status(esa)], [t118_funct_1])).
% 0.46/0.67  thf('30', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ sk_B)
% 0.46/0.67          | ~ (v1_funct_1 @ sk_B)
% 0.46/0.67          | ((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ X0))
% 0.46/0.67              = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.46/0.67                 (k1_funct_1 @ sk_B @ X0)))
% 0.46/0.67          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.67  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('33', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ X0))
% 0.46/0.67            = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.46/0.67               (k1_funct_1 @ sk_B @ X0)))
% 0.46/0.67          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.46/0.67      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.46/0.67  thf('34', plain,
% 0.46/0.67      (((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ sk_A))
% 0.46/0.67         = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['27', '33'])).
% 0.46/0.67  thf('35', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.46/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.67  thf('36', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.46/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.67  thf('37', plain,
% 0.46/0.67      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.67         = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.46/0.67      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.46/0.67  thf('38', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.67      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.67  thf('39', plain, ($false),
% 0.46/0.67      inference('demod', [status(thm)], ['4', '37', '38'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
