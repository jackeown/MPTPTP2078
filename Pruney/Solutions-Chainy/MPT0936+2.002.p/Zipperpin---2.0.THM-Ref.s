%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G3T9ZNRGOW

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:23 EST 2020

% Result     : Theorem 2.88s
% Output     : Refutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 191 expanded)
%              Number of leaves         :   16 (  63 expanded)
%              Depth                    :   19
%              Number of atoms          :  603 (2455 expanded)
%              Number of equality atoms :   62 ( 309 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf('#_fresh_sk1_type',type,(
    '#_fresh_sk1': $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t97_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t97_mcart_1])).

thf('0',plain,(
    ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_mcart_1 @ X21 @ X22 @ X23 )
      = ( k4_tarski @ ( k4_tarski @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_mcart_1 @ X21 @ X22 @ X23 )
      = ( k4_tarski @ ( k4_tarski @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19
        = ( k1_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X19 @ X16 ) @ ( sk_D_1 @ X19 @ X16 ) ) @ X16 )
      | ( r2_hidden @ ( sk_C_1 @ X19 @ X16 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('6',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k4_tarski @ ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) @ ( sk_D_1 @ X1 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_mcart_1 @ X21 @ X22 @ X23 )
      = ( k4_tarski @ ( k4_tarski @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_mcart_1 @ ( sk_C_1 @ X2 @ ( k1_tarski @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k1_tarski @ X0 ) ) @ X1 )
        = ( k4_tarski @ X0 @ X1 ) )
      | ( X2
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k1_tarski @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t28_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_mcart_1 @ A @ B @ C )
        = ( k3_mcart_1 @ D @ E @ F ) )
     => ( ( A = D )
        & ( B = E )
        & ( C = F ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X25 = X24 )
      | ( ( k3_mcart_1 @ X25 @ X28 @ X29 )
       != ( k3_mcart_1 @ X24 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t28_mcart_1])).

thf('12',plain,(
    ! [X25: $i,X28: $i,X29: $i] :
      ( ( '#_fresh_sk1' @ ( k3_mcart_1 @ X25 @ X28 @ X29 ) )
      = X25 ) ),
    inference(inj_rec,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X0 ) )
        = ( sk_C_1 @ X2 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k1_tarski @ X1 ) ) @ X2 )
      | ( X2
        = ( k1_relat_1 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ X1 ) ) )
      | ( ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X2 ) )
        = ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X0 ) )
       != X2 )
      | ( ( sk_C_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) )
        = X2 )
      | ( ( k1_tarski @ X2 )
        = ( k1_relat_1 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k1_tarski @ X1 ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X0 ) ) ) @ ( k1_tarski @ X1 ) )
        = ( '#_fresh_sk1' @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ ( '#_fresh_sk1' @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) ) @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
        = ( '#_fresh_sk1' @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X0 ) ) )
      | ( ( k1_tarski @ ( '#_fresh_sk1' @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X0 ) ) )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['4','17'])).

thf('19',plain,(
    ! [X25: $i,X28: $i,X29: $i] :
      ( ( '#_fresh_sk1' @ ( k3_mcart_1 @ X25 @ X28 @ X29 ) )
      = X25 ) ),
    inference(inj_rec,[status(thm)],['11'])).

thf('20',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_mcart_1 @ X21 @ X22 @ X23 )
      = ( k4_tarski @ ( k4_tarski @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('21',plain,(
    ! [X25: $i,X28: $i,X29: $i] :
      ( ( '#_fresh_sk1' @ ( k3_mcart_1 @ X25 @ X28 @ X29 ) )
      = X25 ) ),
    inference(inj_rec,[status(thm)],['11'])).

thf('22',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_mcart_1 @ X21 @ X22 @ X23 )
      = ( k4_tarski @ ( k4_tarski @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('23',plain,(
    ! [X25: $i,X28: $i,X29: $i] :
      ( ( '#_fresh_sk1' @ ( k3_mcart_1 @ X25 @ X28 @ X29 ) )
      = X25 ) ),
    inference(inj_rec,[status(thm)],['11'])).

thf('24',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
        = X2 )
      | ( ( k1_tarski @ X2 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22','23'])).

thf('25',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
        = X2 )
      | ( ( k1_tarski @ X2 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22','23'])).

thf('26',plain,(
    ! [X16: $i,X19: $i,X20: $i] :
      ( ( X19
        = ( k1_relat_1 @ X16 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X19 @ X16 ) @ X20 ) @ X16 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X19 @ X16 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X1 )
      = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) )
      = ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X1 )
      = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','32'])).

thf('36',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','34','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G3T9ZNRGOW
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 2.88/3.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.88/3.07  % Solved by: fo/fo7.sh
% 2.88/3.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.88/3.07  % done 2534 iterations in 2.620s
% 2.88/3.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.88/3.07  % SZS output start Refutation
% 2.88/3.07  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.88/3.07  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.88/3.07  thf(sk_C_2_type, type, sk_C_2: $i).
% 2.88/3.07  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 2.88/3.07  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.88/3.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.88/3.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.88/3.07  thf(sk_B_type, type, sk_B: $i).
% 2.88/3.07  thf('#_fresh_sk1_type', type, '#_fresh_sk1': $i > $i).
% 2.88/3.07  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 2.88/3.07  thf(sk_A_type, type, sk_A: $i).
% 2.88/3.07  thf(t97_mcart_1, conjecture,
% 2.88/3.07    (![A:$i,B:$i,C:$i]:
% 2.88/3.07     ( ( k1_relat_1 @
% 2.88/3.07         ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 2.88/3.07       ( k1_tarski @ A ) ))).
% 2.88/3.07  thf(zf_stmt_0, negated_conjecture,
% 2.88/3.07    (~( ![A:$i,B:$i,C:$i]:
% 2.88/3.07        ( ( k1_relat_1 @
% 2.88/3.07            ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 2.88/3.07          ( k1_tarski @ A ) ) )),
% 2.88/3.07    inference('cnf.neg', [status(esa)], [t97_mcart_1])).
% 2.88/3.07  thf('0', plain,
% 2.88/3.07      (((k1_relat_1 @ 
% 2.88/3.07         (k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C_2))))
% 2.88/3.07         != (k1_tarski @ sk_A))),
% 2.88/3.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.88/3.07  thf(d3_mcart_1, axiom,
% 2.88/3.07    (![A:$i,B:$i,C:$i]:
% 2.88/3.07     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 2.88/3.07  thf('1', plain,
% 2.88/3.07      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.88/3.07         ((k3_mcart_1 @ X21 @ X22 @ X23)
% 2.88/3.07           = (k4_tarski @ (k4_tarski @ X21 @ X22) @ X23))),
% 2.88/3.07      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.88/3.07  thf(d1_tarski, axiom,
% 2.88/3.07    (![A:$i,B:$i]:
% 2.88/3.07     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 2.88/3.07       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 2.88/3.07  thf('2', plain,
% 2.88/3.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.88/3.07         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 2.88/3.07      inference('cnf', [status(esa)], [d1_tarski])).
% 2.88/3.07  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.88/3.07      inference('simplify', [status(thm)], ['2'])).
% 2.88/3.07  thf('4', plain,
% 2.88/3.07      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.88/3.07         ((k3_mcart_1 @ X21 @ X22 @ X23)
% 2.88/3.07           = (k4_tarski @ (k4_tarski @ X21 @ X22) @ X23))),
% 2.88/3.07      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.88/3.07  thf(d4_relat_1, axiom,
% 2.88/3.07    (![A:$i,B:$i]:
% 2.88/3.07     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 2.88/3.07       ( ![C:$i]:
% 2.88/3.07         ( ( r2_hidden @ C @ B ) <=>
% 2.88/3.07           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 2.88/3.07  thf('5', plain,
% 2.88/3.07      (![X16 : $i, X19 : $i]:
% 2.88/3.07         (((X19) = (k1_relat_1 @ X16))
% 2.88/3.07          | (r2_hidden @ 
% 2.88/3.07             (k4_tarski @ (sk_C_1 @ X19 @ X16) @ (sk_D_1 @ X19 @ X16)) @ X16)
% 2.88/3.07          | (r2_hidden @ (sk_C_1 @ X19 @ X16) @ X19))),
% 2.88/3.07      inference('cnf', [status(esa)], [d4_relat_1])).
% 2.88/3.07  thf('6', plain,
% 2.88/3.07      (![X0 : $i, X2 : $i, X3 : $i]:
% 2.88/3.07         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 2.88/3.07      inference('cnf', [status(esa)], [d1_tarski])).
% 2.88/3.07  thf('7', plain,
% 2.88/3.07      (![X0 : $i, X3 : $i]:
% 2.88/3.07         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 2.88/3.07      inference('simplify', [status(thm)], ['6'])).
% 2.88/3.07  thf('8', plain,
% 2.88/3.07      (![X0 : $i, X1 : $i]:
% 2.88/3.07         ((r2_hidden @ (sk_C_1 @ X1 @ (k1_tarski @ X0)) @ X1)
% 2.88/3.07          | ((X1) = (k1_relat_1 @ (k1_tarski @ X0)))
% 2.88/3.07          | ((k4_tarski @ (sk_C_1 @ X1 @ (k1_tarski @ X0)) @ 
% 2.88/3.07              (sk_D_1 @ X1 @ (k1_tarski @ X0))) = (X0)))),
% 2.88/3.07      inference('sup-', [status(thm)], ['5', '7'])).
% 2.88/3.07  thf('9', plain,
% 2.88/3.07      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.88/3.07         ((k3_mcart_1 @ X21 @ X22 @ X23)
% 2.88/3.07           = (k4_tarski @ (k4_tarski @ X21 @ X22) @ X23))),
% 2.88/3.07      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.88/3.07  thf('10', plain,
% 2.88/3.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.88/3.07         (((k3_mcart_1 @ (sk_C_1 @ X2 @ (k1_tarski @ X0)) @ 
% 2.88/3.07            (sk_D_1 @ X2 @ (k1_tarski @ X0)) @ X1) = (k4_tarski @ X0 @ X1))
% 2.88/3.07          | ((X2) = (k1_relat_1 @ (k1_tarski @ X0)))
% 2.88/3.07          | (r2_hidden @ (sk_C_1 @ X2 @ (k1_tarski @ X0)) @ X2))),
% 2.88/3.07      inference('sup+', [status(thm)], ['8', '9'])).
% 2.88/3.07  thf(t28_mcart_1, axiom,
% 2.88/3.07    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.88/3.07     ( ( ( k3_mcart_1 @ A @ B @ C ) = ( k3_mcart_1 @ D @ E @ F ) ) =>
% 2.88/3.07       ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ))).
% 2.88/3.07  thf('11', plain,
% 2.88/3.07      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.88/3.07         (((X25) = (X24))
% 2.88/3.07          | ((k3_mcart_1 @ X25 @ X28 @ X29) != (k3_mcart_1 @ X24 @ X26 @ X27)))),
% 2.88/3.07      inference('cnf', [status(esa)], [t28_mcart_1])).
% 2.88/3.07  thf('12', plain,
% 2.88/3.07      (![X25 : $i, X28 : $i, X29 : $i]:
% 2.88/3.07         (('#_fresh_sk1' @ (k3_mcart_1 @ X25 @ X28 @ X29)) = (X25))),
% 2.88/3.07      inference('inj_rec', [status(thm)], ['11'])).
% 2.88/3.07  thf('13', plain,
% 2.88/3.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.88/3.07         ((('#_fresh_sk1' @ (k4_tarski @ X1 @ X0))
% 2.88/3.07            = (sk_C_1 @ X2 @ (k1_tarski @ X1)))
% 2.88/3.07          | (r2_hidden @ (sk_C_1 @ X2 @ (k1_tarski @ X1)) @ X2)
% 2.88/3.07          | ((X2) = (k1_relat_1 @ (k1_tarski @ X1))))),
% 2.88/3.07      inference('sup+', [status(thm)], ['10', '12'])).
% 2.88/3.07  thf('14', plain,
% 2.88/3.07      (![X0 : $i, X3 : $i]:
% 2.88/3.07         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 2.88/3.07      inference('simplify', [status(thm)], ['6'])).
% 2.88/3.07  thf('15', plain,
% 2.88/3.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.88/3.07         (((k1_tarski @ X0) = (k1_relat_1 @ (k1_tarski @ X1)))
% 2.88/3.07          | (('#_fresh_sk1' @ (k4_tarski @ X1 @ X2))
% 2.88/3.07              = (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 2.88/3.07          | ((sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)) = (X0)))),
% 2.88/3.07      inference('sup-', [status(thm)], ['13', '14'])).
% 2.88/3.07  thf('16', plain,
% 2.88/3.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.88/3.07         ((('#_fresh_sk1' @ (k4_tarski @ X1 @ X0)) != (X2))
% 2.88/3.07          | ((sk_C_1 @ (k1_tarski @ X2) @ (k1_tarski @ X1)) = (X2))
% 2.88/3.07          | ((k1_tarski @ X2) = (k1_relat_1 @ (k1_tarski @ X1))))),
% 2.88/3.07      inference('eq_fact', [status(thm)], ['15'])).
% 2.88/3.07  thf('17', plain,
% 2.88/3.07      (![X0 : $i, X1 : $i]:
% 2.88/3.07         (((k1_tarski @ ('#_fresh_sk1' @ (k4_tarski @ X1 @ X0)))
% 2.88/3.07            = (k1_relat_1 @ (k1_tarski @ X1)))
% 2.88/3.07          | ((sk_C_1 @ (k1_tarski @ ('#_fresh_sk1' @ (k4_tarski @ X1 @ X0))) @ 
% 2.88/3.07              (k1_tarski @ X1)) = ('#_fresh_sk1' @ (k4_tarski @ X1 @ X0))))),
% 2.88/3.07      inference('simplify', [status(thm)], ['16'])).
% 2.88/3.07  thf('18', plain,
% 2.88/3.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.88/3.07         (((sk_C_1 @ 
% 2.88/3.07            (k1_tarski @ ('#_fresh_sk1' @ (k3_mcart_1 @ X2 @ X1 @ X0))) @ 
% 2.88/3.07            (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 2.88/3.07            = ('#_fresh_sk1' @ (k4_tarski @ (k4_tarski @ X2 @ X1) @ X0)))
% 2.88/3.07          | ((k1_tarski @ 
% 2.88/3.07              ('#_fresh_sk1' @ (k4_tarski @ (k4_tarski @ X2 @ X1) @ X0)))
% 2.88/3.07              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)))))),
% 2.88/3.07      inference('sup+', [status(thm)], ['4', '17'])).
% 2.88/3.07  thf('19', plain,
% 2.88/3.07      (![X25 : $i, X28 : $i, X29 : $i]:
% 2.88/3.07         (('#_fresh_sk1' @ (k3_mcart_1 @ X25 @ X28 @ X29)) = (X25))),
% 2.88/3.07      inference('inj_rec', [status(thm)], ['11'])).
% 2.88/3.07  thf('20', plain,
% 2.88/3.07      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.88/3.07         ((k3_mcart_1 @ X21 @ X22 @ X23)
% 2.88/3.07           = (k4_tarski @ (k4_tarski @ X21 @ X22) @ X23))),
% 2.88/3.07      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.88/3.07  thf('21', plain,
% 2.88/3.07      (![X25 : $i, X28 : $i, X29 : $i]:
% 2.88/3.07         (('#_fresh_sk1' @ (k3_mcart_1 @ X25 @ X28 @ X29)) = (X25))),
% 2.88/3.07      inference('inj_rec', [status(thm)], ['11'])).
% 2.88/3.07  thf('22', plain,
% 2.88/3.07      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.88/3.07         ((k3_mcart_1 @ X21 @ X22 @ X23)
% 2.88/3.07           = (k4_tarski @ (k4_tarski @ X21 @ X22) @ X23))),
% 2.88/3.07      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.88/3.07  thf('23', plain,
% 2.88/3.07      (![X25 : $i, X28 : $i, X29 : $i]:
% 2.88/3.07         (('#_fresh_sk1' @ (k3_mcart_1 @ X25 @ X28 @ X29)) = (X25))),
% 2.88/3.07      inference('inj_rec', [status(thm)], ['11'])).
% 2.88/3.07  thf('24', plain,
% 2.88/3.07      (![X1 : $i, X2 : $i]:
% 2.88/3.07         (((sk_C_1 @ (k1_tarski @ X2) @ (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 2.88/3.07            = (X2))
% 2.88/3.07          | ((k1_tarski @ X2)
% 2.88/3.07              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)))))),
% 2.88/3.07      inference('demod', [status(thm)], ['18', '19', '20', '21', '22', '23'])).
% 2.88/3.07  thf('25', plain,
% 2.88/3.07      (![X1 : $i, X2 : $i]:
% 2.88/3.07         (((sk_C_1 @ (k1_tarski @ X2) @ (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 2.88/3.07            = (X2))
% 2.88/3.07          | ((k1_tarski @ X2)
% 2.88/3.07              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)))))),
% 2.88/3.07      inference('demod', [status(thm)], ['18', '19', '20', '21', '22', '23'])).
% 2.88/3.07  thf('26', plain,
% 2.88/3.07      (![X16 : $i, X19 : $i, X20 : $i]:
% 2.88/3.07         (((X19) = (k1_relat_1 @ X16))
% 2.88/3.07          | ~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X19 @ X16) @ X20) @ X16)
% 2.88/3.07          | ~ (r2_hidden @ (sk_C_1 @ X19 @ X16) @ X19))),
% 2.88/3.07      inference('cnf', [status(esa)], [d4_relat_1])).
% 2.88/3.07  thf('27', plain,
% 2.88/3.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.88/3.07         (~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 2.88/3.07             (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 2.88/3.07          | ((k1_tarski @ X0)
% 2.88/3.07              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 2.88/3.07          | ~ (r2_hidden @ 
% 2.88/3.07               (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ 
% 2.88/3.07               (k1_tarski @ X0))
% 2.88/3.07          | ((k1_tarski @ X0)
% 2.88/3.07              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 2.88/3.07      inference('sup-', [status(thm)], ['25', '26'])).
% 2.88/3.07  thf('28', plain,
% 2.88/3.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.88/3.07         (~ (r2_hidden @ 
% 2.88/3.07             (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ 
% 2.88/3.07             (k1_tarski @ X0))
% 2.88/3.07          | ((k1_tarski @ X0)
% 2.88/3.07              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 2.88/3.07          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 2.88/3.07               (k1_tarski @ (k4_tarski @ X0 @ X1))))),
% 2.88/3.07      inference('simplify', [status(thm)], ['27'])).
% 2.88/3.07  thf('29', plain,
% 2.88/3.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.88/3.07         (~ (r2_hidden @ X0 @ (k1_tarski @ X0))
% 2.88/3.07          | ((k1_tarski @ X0)
% 2.88/3.07              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 2.88/3.07          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 2.88/3.07               (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 2.88/3.07          | ((k1_tarski @ X0)
% 2.88/3.07              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 2.88/3.07      inference('sup-', [status(thm)], ['24', '28'])).
% 2.88/3.07  thf('30', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.88/3.07      inference('simplify', [status(thm)], ['2'])).
% 2.88/3.07  thf('31', plain,
% 2.88/3.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.88/3.07         (((k1_tarski @ X0)
% 2.88/3.07            = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 2.88/3.07          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 2.88/3.07               (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 2.88/3.07          | ((k1_tarski @ X0)
% 2.88/3.07              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 2.88/3.07      inference('demod', [status(thm)], ['29', '30'])).
% 2.88/3.07  thf('32', plain,
% 2.88/3.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.88/3.07         (~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 2.88/3.07             (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 2.88/3.07          | ((k1_tarski @ X0)
% 2.88/3.07              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 2.88/3.07      inference('simplify', [status(thm)], ['31'])).
% 2.88/3.07  thf('33', plain,
% 2.88/3.07      (![X0 : $i, X1 : $i]:
% 2.88/3.07         ((k1_tarski @ X1) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 2.88/3.07      inference('sup-', [status(thm)], ['3', '32'])).
% 2.88/3.07  thf('34', plain,
% 2.88/3.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.88/3.07         ((k1_tarski @ (k4_tarski @ X2 @ X1))
% 2.88/3.07           = (k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0))))),
% 2.88/3.07      inference('sup+', [status(thm)], ['1', '33'])).
% 2.88/3.07  thf('35', plain,
% 2.88/3.07      (![X0 : $i, X1 : $i]:
% 2.88/3.07         ((k1_tarski @ X1) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 2.88/3.07      inference('sup-', [status(thm)], ['3', '32'])).
% 2.88/3.07  thf('36', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 2.88/3.07      inference('demod', [status(thm)], ['0', '34', '35'])).
% 2.88/3.07  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 2.88/3.07  
% 2.88/3.07  % SZS output end Refutation
% 2.88/3.07  
% 2.88/3.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
