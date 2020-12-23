%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tt20JAAlWK

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 111 expanded)
%              Number of leaves         :   21 (  41 expanded)
%              Depth                    :   16
%              Number of atoms          :  584 (1360 expanded)
%              Number of equality atoms :   49 ( 103 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k11_relat_1 @ X11 @ X12 )
        = ( k9_relat_1 @ X11 @ ( k1_tarski @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k9_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t168_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
         => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t168_funct_1])).

thf('2',plain,(
    ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
        = X0 )
      | ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k11_relat_1 @ X16 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
        = X2 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( X21
        = ( k1_funct_1 @ X19 @ X18 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X21 ) @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B )
      | ( X0
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B )
      | ( X0
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k11_relat_1 @ sk_B @ sk_A )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ X0 )
        = X0 )
      | ( ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ X0 )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ sk_B @ sk_A )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ X0 )
        = X0 )
      | ( ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ X0 )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ X0 )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ sk_A )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
       != X0 )
      | ~ ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ X18 @ X21 ) @ X19 )
      | ( X21
       != ( k1_funct_1 @ X19 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( r2_hidden @ ( k4_tarski @ X18 @ ( k1_funct_1 @ X19 @ X18 ) ) @ X19 )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_B @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X17 @ X15 ) @ X16 )
      | ( r2_hidden @ X15 @ ( k11_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k11_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','32'])).

thf('34',plain,
    ( ( ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( ( sk_C @ ( k11_relat_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('36',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k11_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['5','36'])).

thf('38',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != ( k11_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != ( k11_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tt20JAAlWK
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:34:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 80 iterations in 0.077s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.51  thf(d16_relat_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (![X11 : $i, X12 : $i]:
% 0.22/0.51         (((k11_relat_1 @ X11 @ X12) = (k9_relat_1 @ X11 @ (k1_tarski @ X12)))
% 0.22/0.51          | ~ (v1_relat_1 @ X11))),
% 0.22/0.51      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.22/0.51  thf(t148_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ B ) =>
% 0.22/0.51       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (![X13 : $i, X14 : $i]:
% 0.22/0.51         (((k2_relat_1 @ (k7_relat_1 @ X13 @ X14)) = (k9_relat_1 @ X13 @ X14))
% 0.22/0.51          | ~ (v1_relat_1 @ X13))),
% 0.22/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.51  thf(t168_funct_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.51       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.51         ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) =
% 0.22/0.51           ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i]:
% 0.22/0.51        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.51          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.51            ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) =
% 0.22/0.51              ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t168_funct_1])).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (((k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)))
% 0.22/0.51         != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.22/0.51          != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.22/0.51        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.22/0.51         != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.51  thf(d1_tarski, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X0 : $i, X4 : $i]:
% 0.22/0.51         (((X4) = (k1_tarski @ X0))
% 0.22/0.51          | ((sk_C @ X4 @ X0) = (X0))
% 0.22/0.51          | (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.51  thf(t204_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ C ) =>
% 0.22/0.51       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.51         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X15 @ (k11_relat_1 @ X16 @ X17))
% 0.22/0.51          | (r2_hidden @ (k4_tarski @ X17 @ X15) @ X16)
% 0.22/0.51          | ~ (v1_relat_1 @ X16))),
% 0.22/0.51      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (((sk_C @ (k11_relat_1 @ X1 @ X0) @ X2) = (X2))
% 0.22/0.51          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 0.22/0.51          | ~ (v1_relat_1 @ X1)
% 0.22/0.51          | (r2_hidden @ 
% 0.22/0.51             (k4_tarski @ X0 @ (sk_C @ (k11_relat_1 @ X1 @ X0) @ X2)) @ X1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.51  thf('9', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d4_funct_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.51       ( ![B:$i,C:$i]:
% 0.22/0.51         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.22/0.51             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.22/0.51               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.51           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.22/0.51             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.22/0.51               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X18 @ (k1_relat_1 @ X19))
% 0.22/0.51          | ((X21) = (k1_funct_1 @ X19 @ X18))
% 0.22/0.51          | ~ (r2_hidden @ (k4_tarski @ X18 @ X21) @ X19)
% 0.22/0.51          | ~ (v1_funct_1 @ X19)
% 0.22/0.51          | ~ (v1_relat_1 @ X19))),
% 0.22/0.51      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ sk_B)
% 0.22/0.51          | ~ (v1_funct_1 @ sk_B)
% 0.22/0.51          | ~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B)
% 0.22/0.51          | ((X0) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('13', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B)
% 0.22/0.51          | ((X0) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ sk_B)
% 0.22/0.51          | ((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ X0))
% 0.22/0.51          | ((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ X0) = (X0))
% 0.22/0.51          | ((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ X0)
% 0.22/0.51              = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['8', '14'])).
% 0.22/0.51  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ X0))
% 0.22/0.51          | ((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ X0) = (X0))
% 0.22/0.51          | ((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ X0)
% 0.22/0.51              = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (((X0) != (k1_funct_1 @ sk_B @ sk_A))
% 0.22/0.51          | ((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ X0)
% 0.22/0.51              = (k1_funct_1 @ sk_B @ sk_A))
% 0.22/0.51          | ((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ X0)))),
% 0.22/0.51      inference('eq_fact', [status(thm)], ['17'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.22/0.51        | ((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A))
% 0.22/0.51            = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X0 : $i, X4 : $i]:
% 0.22/0.51         (((X4) = (k1_tarski @ X0))
% 0.22/0.51          | ((sk_C @ X4 @ X0) != (X0))
% 0.22/0.51          | ~ (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      ((~ (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k11_relat_1 @ sk_B @ sk_A))
% 0.22/0.51        | ((k11_relat_1 @ sk_B @ sk_A)
% 0.22/0.51            = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.22/0.51        | ((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A))
% 0.22/0.51            != (k1_funct_1 @ sk_B @ sk_A))
% 0.22/0.51        | ((k11_relat_1 @ sk_B @ sk_A)
% 0.22/0.51            = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf('22', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X18 @ (k1_relat_1 @ X19))
% 0.22/0.51          | (r2_hidden @ (k4_tarski @ X18 @ X21) @ X19)
% 0.22/0.51          | ((X21) != (k1_funct_1 @ X19 @ X18))
% 0.22/0.51          | ~ (v1_funct_1 @ X19)
% 0.22/0.51          | ~ (v1_relat_1 @ X19))),
% 0.22/0.51      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X18 : $i, X19 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X19)
% 0.22/0.51          | ~ (v1_funct_1 @ X19)
% 0.22/0.51          | (r2_hidden @ (k4_tarski @ X18 @ (k1_funct_1 @ X19 @ X18)) @ X19)
% 0.22/0.51          | ~ (r2_hidden @ X18 @ (k1_relat_1 @ X19)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['23'])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)
% 0.22/0.51        | ~ (v1_funct_1 @ sk_B)
% 0.22/0.51        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['22', '24'])).
% 0.22/0.51  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('28', plain,
% 0.22/0.51      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_B @ sk_A)) @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.51         (~ (r2_hidden @ (k4_tarski @ X17 @ X15) @ X16)
% 0.22/0.51          | (r2_hidden @ X15 @ (k11_relat_1 @ X16 @ X17))
% 0.22/0.51          | ~ (v1_relat_1 @ X16))),
% 0.22/0.51      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      ((~ (v1_relat_1 @ sk_B)
% 0.22/0.51        | (r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k11_relat_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.51  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      ((r2_hidden @ (k1_funct_1 @ sk_B @ sk_A) @ (k11_relat_1 @ sk_B @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.22/0.51        | ((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A))
% 0.22/0.51            != (k1_funct_1 @ sk_B @ sk_A))
% 0.22/0.51        | ((k11_relat_1 @ sk_B @ sk_A)
% 0.22/0.51            = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['21', '32'])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      ((((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A))
% 0.22/0.51          != (k1_funct_1 @ sk_B @ sk_A))
% 0.22/0.51        | ((k11_relat_1 @ sk_B @ sk_A)
% 0.22/0.51            = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.22/0.51      inference('simplify', [status(thm)], ['33'])).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.22/0.51        | ((sk_C @ (k11_relat_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A))
% 0.22/0.51            = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (((k11_relat_1 @ sk_B @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('clc', [status(thm)], ['34', '35'])).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k11_relat_1 @ sk_B @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['5', '36'])).
% 0.22/0.51  thf('38', plain,
% 0.22/0.51      ((((k11_relat_1 @ sk_B @ sk_A) != (k11_relat_1 @ sk_B @ sk_A))
% 0.22/0.51        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '37'])).
% 0.22/0.51  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('40', plain,
% 0.22/0.51      (((k11_relat_1 @ sk_B @ sk_A) != (k11_relat_1 @ sk_B @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.51  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
