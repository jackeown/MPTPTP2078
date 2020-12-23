%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GCCL1rlBFT

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:00 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   52 (  74 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :   16
%              Number of atoms          :  602 ( 917 expanded)
%              Number of equality atoms :   35 (  54 expanded)
%              Maximal formula depth    :   17 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(d13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X0 @ X1 @ X2 ) @ ( sk_D @ X0 @ X1 @ X2 ) ) @ X2 )
      | ( X0
        = ( k9_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ( X11
       != ( k2_relat_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ ( k2_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X12 @ X10 ) @ X12 ) @ X10 )
      | ( X11
       != ( k2_relat_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('7',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X12 @ X10 ) @ X12 ) @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_D @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ X0 ) @ ( sk_D @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(d7_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( B
              = ( k4_relat_1 @ A ) )
          <=> ! [C: $i,D: $i] :
                ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( X15
       != ( k4_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X18 ) @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X17 ) @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X18 ) @ ( k4_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ ( sk_D_2 @ ( sk_D @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ X0 ) ) @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ ( sk_D_2 @ ( sk_D @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ X0 ) ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ ( k2_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_D @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ X0 ) @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ ( sk_D @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ X0 ) @ ( sk_D @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X2 ) @ X0 )
      | ~ ( r2_hidden @ X3 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_D @ X0 @ X1 @ X2 ) ) @ X2 )
      | ( X0
        = ( k9_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D_2 @ ( sk_D @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D_2 @ ( sk_D @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_D_2 @ ( sk_D @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D_2 @ ( sk_D @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ X0 ) @ X1 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t146_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
          = ( k2_relat_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_relat_1])).

thf('29',plain,(
    ( k9_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) )
 != ( k2_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ( k2_relat_1 @ sk_A )
 != ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GCCL1rlBFT
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:21:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.59/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.77  % Solved by: fo/fo7.sh
% 0.59/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.77  % done 295 iterations in 0.309s
% 0.59/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.77  % SZS output start Refutation
% 0.59/0.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.77  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.59/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.77  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.59/0.77  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.59/0.77  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.59/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.77  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.59/0.77  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.59/0.77  thf(t37_relat_1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ A ) =>
% 0.59/0.77       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.59/0.77         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.59/0.77  thf('0', plain,
% 0.59/0.77      (![X21 : $i]:
% 0.59/0.77         (((k1_relat_1 @ X21) = (k2_relat_1 @ (k4_relat_1 @ X21)))
% 0.59/0.77          | ~ (v1_relat_1 @ X21))),
% 0.59/0.77      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.59/0.77  thf(d13_relat_1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ A ) =>
% 0.59/0.77       ( ![B:$i,C:$i]:
% 0.59/0.77         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.59/0.77           ( ![D:$i]:
% 0.59/0.77             ( ( r2_hidden @ D @ C ) <=>
% 0.59/0.77               ( ?[E:$i]:
% 0.59/0.77                 ( ( r2_hidden @ E @ B ) & 
% 0.59/0.77                   ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) ) ) ))).
% 0.59/0.77  thf('1', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((r2_hidden @ (sk_D @ X0 @ X1 @ X2) @ X0)
% 0.59/0.77          | (r2_hidden @ 
% 0.59/0.77             (k4_tarski @ (sk_E @ X0 @ X1 @ X2) @ (sk_D @ X0 @ X1 @ X2)) @ X2)
% 0.59/0.77          | ((X0) = (k9_relat_1 @ X2 @ X1))
% 0.59/0.77          | ~ (v1_relat_1 @ X2))),
% 0.59/0.77      inference('cnf', [status(esa)], [d13_relat_1])).
% 0.59/0.77  thf(d5_relat_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.59/0.77       ( ![C:$i]:
% 0.59/0.77         ( ( r2_hidden @ C @ B ) <=>
% 0.59/0.77           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.59/0.77  thf('2', plain,
% 0.59/0.77      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.59/0.77         (~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10)
% 0.59/0.77          | (r2_hidden @ X9 @ X11)
% 0.59/0.77          | ((X11) != (k2_relat_1 @ X10)))),
% 0.59/0.77      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.59/0.77  thf('3', plain,
% 0.59/0.77      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.59/0.77         ((r2_hidden @ X9 @ (k2_relat_1 @ X10))
% 0.59/0.77          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10))),
% 0.59/0.77      inference('simplify', [status(thm)], ['2'])).
% 0.59/0.77  thf('4', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X0)
% 0.59/0.77          | ((X2) = (k9_relat_1 @ X0 @ X1))
% 0.59/0.77          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.59/0.77          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['1', '3'])).
% 0.59/0.77  thf('5', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((r2_hidden @ (sk_D @ (k2_relat_1 @ X0) @ X1 @ X0) @ (k2_relat_1 @ X0))
% 0.59/0.77          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1))
% 0.59/0.77          | ~ (v1_relat_1 @ X0))),
% 0.59/0.77      inference('eq_fact', [status(thm)], ['4'])).
% 0.59/0.77  thf('6', plain,
% 0.59/0.77      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.77         (~ (r2_hidden @ X12 @ X11)
% 0.59/0.77          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X12 @ X10) @ X12) @ X10)
% 0.59/0.77          | ((X11) != (k2_relat_1 @ X10)))),
% 0.59/0.77      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.59/0.77  thf('7', plain,
% 0.59/0.77      (![X10 : $i, X12 : $i]:
% 0.59/0.77         ((r2_hidden @ (k4_tarski @ (sk_D_2 @ X12 @ X10) @ X12) @ X10)
% 0.59/0.77          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X10)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['6'])).
% 0.59/0.77  thf('8', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X0)
% 0.59/0.77          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1))
% 0.59/0.77          | (r2_hidden @ 
% 0.59/0.77             (k4_tarski @ 
% 0.59/0.77              (sk_D_2 @ (sk_D @ (k2_relat_1 @ X0) @ X1 @ X0) @ X0) @ 
% 0.59/0.77              (sk_D @ (k2_relat_1 @ X0) @ X1 @ X0)) @ 
% 0.59/0.77             X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['5', '7'])).
% 0.59/0.77  thf(dt_k4_relat_1, axiom,
% 0.59/0.77    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.59/0.77  thf('9', plain,
% 0.59/0.77      (![X20 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X20)) | ~ (v1_relat_1 @ X20))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.59/0.77  thf(d7_relat_1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ A ) =>
% 0.59/0.77       ( ![B:$i]:
% 0.59/0.77         ( ( v1_relat_1 @ B ) =>
% 0.59/0.77           ( ( ( B ) = ( k4_relat_1 @ A ) ) <=>
% 0.59/0.77             ( ![C:$i,D:$i]:
% 0.59/0.77               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.59/0.77                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) ) ))).
% 0.59/0.77  thf('10', plain,
% 0.59/0.77      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X15)
% 0.59/0.77          | ((X15) != (k4_relat_1 @ X16))
% 0.59/0.77          | (r2_hidden @ (k4_tarski @ X17 @ X18) @ X15)
% 0.59/0.77          | ~ (r2_hidden @ (k4_tarski @ X18 @ X17) @ X16)
% 0.59/0.77          | ~ (v1_relat_1 @ X16))),
% 0.59/0.77      inference('cnf', [status(esa)], [d7_relat_1])).
% 0.59/0.77  thf('11', plain,
% 0.59/0.77      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X16)
% 0.59/0.77          | ~ (r2_hidden @ (k4_tarski @ X18 @ X17) @ X16)
% 0.59/0.77          | (r2_hidden @ (k4_tarski @ X17 @ X18) @ (k4_relat_1 @ X16))
% 0.59/0.77          | ~ (v1_relat_1 @ (k4_relat_1 @ X16)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['10'])).
% 0.59/0.77  thf('12', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X0)
% 0.59/0.77          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.59/0.77          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['9', '11'])).
% 0.59/0.77  thf('13', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.59/0.77          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.59/0.77          | ~ (v1_relat_1 @ X0))),
% 0.59/0.77      inference('simplify', [status(thm)], ['12'])).
% 0.59/0.77  thf('14', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1))
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | (r2_hidden @ 
% 0.59/0.77             (k4_tarski @ (sk_D @ (k2_relat_1 @ X0) @ X1 @ X0) @ 
% 0.59/0.77              (sk_D_2 @ (sk_D @ (k2_relat_1 @ X0) @ X1 @ X0) @ X0)) @ 
% 0.59/0.77             (k4_relat_1 @ X0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['8', '13'])).
% 0.59/0.77  thf('15', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((r2_hidden @ 
% 0.59/0.77           (k4_tarski @ (sk_D @ (k2_relat_1 @ X0) @ X1 @ X0) @ 
% 0.59/0.77            (sk_D_2 @ (sk_D @ (k2_relat_1 @ X0) @ X1 @ X0) @ X0)) @ 
% 0.59/0.77           (k4_relat_1 @ X0))
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['14'])).
% 0.59/0.77  thf('16', plain,
% 0.59/0.77      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.59/0.77         ((r2_hidden @ X9 @ (k2_relat_1 @ X10))
% 0.59/0.77          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10))),
% 0.59/0.77      inference('simplify', [status(thm)], ['2'])).
% 0.59/0.77  thf('17', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1))
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | (r2_hidden @ 
% 0.59/0.77             (sk_D_2 @ (sk_D @ (k2_relat_1 @ X0) @ X1 @ X0) @ X0) @ 
% 0.59/0.77             (k2_relat_1 @ (k4_relat_1 @ X0))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['15', '16'])).
% 0.59/0.77  thf('18', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((r2_hidden @ (sk_D @ (k2_relat_1 @ X0) @ X1 @ X0) @ (k2_relat_1 @ X0))
% 0.59/0.77          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1))
% 0.59/0.77          | ~ (v1_relat_1 @ X0))),
% 0.59/0.77      inference('eq_fact', [status(thm)], ['4'])).
% 0.59/0.77  thf('19', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X0)
% 0.59/0.77          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1))
% 0.59/0.77          | (r2_hidden @ 
% 0.59/0.77             (k4_tarski @ 
% 0.59/0.77              (sk_D_2 @ (sk_D @ (k2_relat_1 @ X0) @ X1 @ X0) @ X0) @ 
% 0.59/0.77              (sk_D @ (k2_relat_1 @ X0) @ X1 @ X0)) @ 
% 0.59/0.77             X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['5', '7'])).
% 0.59/0.77  thf('20', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.77         (~ (r2_hidden @ (sk_D @ X0 @ X1 @ X2) @ X0)
% 0.59/0.77          | ~ (r2_hidden @ X3 @ X1)
% 0.59/0.77          | ~ (r2_hidden @ (k4_tarski @ X3 @ (sk_D @ X0 @ X1 @ X2)) @ X2)
% 0.59/0.77          | ((X0) = (k9_relat_1 @ X2 @ X1))
% 0.59/0.77          | ~ (v1_relat_1 @ X2))),
% 0.59/0.77      inference('cnf', [status(esa)], [d13_relat_1])).
% 0.59/0.77  thf('21', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1))
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1))
% 0.59/0.77          | ~ (r2_hidden @ 
% 0.59/0.77               (sk_D_2 @ (sk_D @ (k2_relat_1 @ X0) @ X1 @ X0) @ X0) @ X1)
% 0.59/0.77          | ~ (r2_hidden @ (sk_D @ (k2_relat_1 @ X0) @ X1 @ X0) @ 
% 0.59/0.77               (k2_relat_1 @ X0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.77  thf('22', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (r2_hidden @ (sk_D @ (k2_relat_1 @ X0) @ X1 @ X0) @ 
% 0.59/0.77             (k2_relat_1 @ X0))
% 0.59/0.77          | ~ (r2_hidden @ 
% 0.59/0.77               (sk_D_2 @ (sk_D @ (k2_relat_1 @ X0) @ X1 @ X0) @ X0) @ X1)
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['21'])).
% 0.59/0.77  thf('23', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X0)
% 0.59/0.77          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1))
% 0.59/0.77          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1))
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (r2_hidden @ 
% 0.59/0.77               (sk_D_2 @ (sk_D @ (k2_relat_1 @ X0) @ X1 @ X0) @ X0) @ X1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['18', '22'])).
% 0.59/0.77  thf('24', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (r2_hidden @ 
% 0.59/0.77             (sk_D_2 @ (sk_D @ (k2_relat_1 @ X0) @ X1 @ X0) @ X0) @ X1)
% 0.59/0.77          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1))
% 0.59/0.77          | ~ (v1_relat_1 @ X0))),
% 0.59/0.77      inference('simplify', [status(thm)], ['23'])).
% 0.59/0.77  thf('25', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X0)
% 0.59/0.77          | ((k2_relat_1 @ X0)
% 0.59/0.77              = (k9_relat_1 @ X0 @ (k2_relat_1 @ (k4_relat_1 @ X0))))
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ((k2_relat_1 @ X0)
% 0.59/0.77              = (k9_relat_1 @ X0 @ (k2_relat_1 @ (k4_relat_1 @ X0)))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['17', '24'])).
% 0.59/0.77  thf('26', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (((k2_relat_1 @ X0)
% 0.59/0.77            = (k9_relat_1 @ X0 @ (k2_relat_1 @ (k4_relat_1 @ X0))))
% 0.59/0.77          | ~ (v1_relat_1 @ X0))),
% 0.59/0.77      inference('simplify', [status(thm)], ['25'])).
% 0.59/0.77  thf('27', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['0', '26'])).
% 0.59/0.77  thf('28', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X0)
% 0.59/0.77          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.59/0.77      inference('simplify', [status(thm)], ['27'])).
% 0.59/0.77  thf(t146_relat_1, conjecture,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ A ) =>
% 0.59/0.77       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.59/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.77    (~( ![A:$i]:
% 0.59/0.77        ( ( v1_relat_1 @ A ) =>
% 0.59/0.77          ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ) )),
% 0.59/0.77    inference('cnf.neg', [status(esa)], [t146_relat_1])).
% 0.59/0.77  thf('29', plain,
% 0.59/0.77      (((k9_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)) != (k2_relat_1 @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('30', plain,
% 0.59/0.77      ((((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['28', '29'])).
% 0.59/0.77  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('32', plain, (((k2_relat_1 @ sk_A) != (k2_relat_1 @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['30', '31'])).
% 0.59/0.77  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
