%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u9ZaJ6yNty

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:40 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   66 (  96 expanded)
%              Number of leaves         :   18 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  582 ( 931 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t204_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
        <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t204_relat_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k11_relat_1 @ X15 @ X16 )
        = ( k9_relat_1 @ X15 @ ( k1_tarski @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('5',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

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

thf('9',plain,(
    ! [X8: $i,X9: $i,X11: $i,X13: $i,X14: $i] :
      ( ( X11
       != ( k9_relat_1 @ X9 @ X8 ) )
      | ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X13 ) @ X9 )
      | ~ ( r2_hidden @ X14 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('10',plain,(
    ! [X8: $i,X9: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( r2_hidden @ X14 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X13 ) @ X9 )
      | ( r2_hidden @ X13 @ ( k9_relat_1 @ X9 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ ( k9_relat_1 @ sk_C @ X0 ) )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ ( k9_relat_1 @ sk_C @ X0 ) )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_hidden @ sk_B @ ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,
    ( ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['2','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
   <= ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k11_relat_1 @ X15 @ X16 )
        = ( k9_relat_1 @ X15 @ ( k1_tarski @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k9_relat_1 @ X20 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X20 @ X18 @ X19 ) @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ) @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ) @ sk_C )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('30',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k11_relat_1 @ X15 @ X16 )
        = ( k9_relat_1 @ X15 @ ( k1_tarski @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k9_relat_1 @ X20 @ X18 ) )
      | ( r2_hidden @ ( sk_D_2 @ X20 @ X18 @ X19 ) @ X18 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( sk_D_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('38',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('39',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( sk_D_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B )
      = sk_A )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','19','20','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u9ZaJ6yNty
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:19:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 63 iterations in 0.062s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.56  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.38/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.38/0.56  thf(t204_relat_1, conjecture,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ C ) =>
% 0.38/0.56       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.38/0.56         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.56        ( ( v1_relat_1 @ C ) =>
% 0.38/0.56          ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.38/0.56            ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t204_relat_1])).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      ((~ (r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))
% 0.38/0.56        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      (~ ((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))) | 
% 0.38/0.56       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.38/0.56      inference('split', [status(esa)], ['0'])).
% 0.38/0.56  thf(d16_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (![X15 : $i, X16 : $i]:
% 0.38/0.56         (((k11_relat_1 @ X15 @ X16) = (k9_relat_1 @ X15 @ (k1_tarski @ X16)))
% 0.38/0.56          | ~ (v1_relat_1 @ X15))),
% 0.38/0.56      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.38/0.56  thf(t69_enumset1, axiom,
% 0.38/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.56  thf('3', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.38/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.56  thf(d2_tarski, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.38/0.56       ( ![D:$i]:
% 0.38/0.56         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.56         (((X1) != (X0))
% 0.38/0.56          | (r2_hidden @ X1 @ X2)
% 0.38/0.56          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_tarski])).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['4'])).
% 0.38/0.56  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['3', '5'])).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))
% 0.38/0.56        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.38/0.56         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.38/0.56      inference('split', [status(esa)], ['7'])).
% 0.38/0.56  thf(d13_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ A ) =>
% 0.38/0.56       ( ![B:$i,C:$i]:
% 0.38/0.56         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.38/0.56           ( ![D:$i]:
% 0.38/0.56             ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.56               ( ?[E:$i]:
% 0.38/0.56                 ( ( r2_hidden @ E @ B ) & 
% 0.38/0.56                   ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      (![X8 : $i, X9 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 0.38/0.56         (((X11) != (k9_relat_1 @ X9 @ X8))
% 0.38/0.56          | (r2_hidden @ X13 @ X11)
% 0.38/0.56          | ~ (r2_hidden @ (k4_tarski @ X14 @ X13) @ X9)
% 0.38/0.56          | ~ (r2_hidden @ X14 @ X8)
% 0.38/0.56          | ~ (v1_relat_1 @ X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [d13_relat_1])).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (![X8 : $i, X9 : $i, X13 : $i, X14 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X9)
% 0.38/0.56          | ~ (r2_hidden @ X14 @ X8)
% 0.38/0.56          | ~ (r2_hidden @ (k4_tarski @ X14 @ X13) @ X9)
% 0.38/0.56          | (r2_hidden @ X13 @ (k9_relat_1 @ X9 @ X8)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['9'])).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          ((r2_hidden @ sk_B @ (k9_relat_1 @ sk_C @ X0))
% 0.38/0.56           | ~ (r2_hidden @ sk_A @ X0)
% 0.38/0.56           | ~ (v1_relat_1 @ sk_C)))
% 0.38/0.56         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['8', '10'])).
% 0.38/0.56  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          ((r2_hidden @ sk_B @ (k9_relat_1 @ sk_C @ X0))
% 0.38/0.56           | ~ (r2_hidden @ sk_A @ X0)))
% 0.38/0.56         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.38/0.56      inference('demod', [status(thm)], ['11', '12'])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (((r2_hidden @ sk_B @ (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A))))
% 0.38/0.56         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['6', '13'])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      ((((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))
% 0.38/0.56         | ~ (v1_relat_1 @ sk_C)))
% 0.38/0.56         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['2', '14'])).
% 0.38/0.56  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A)))
% 0.38/0.56         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.38/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      ((~ (r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A)))
% 0.38/0.56         <= (~ ((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.38/0.56      inference('split', [status(esa)], ['0'])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))) | 
% 0.38/0.56       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.38/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))) | 
% 0.38/0.56       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.38/0.56      inference('split', [status(esa)], ['7'])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A)))
% 0.38/0.56         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.38/0.56      inference('split', [status(esa)], ['7'])).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      (![X15 : $i, X16 : $i]:
% 0.38/0.56         (((k11_relat_1 @ X15 @ X16) = (k9_relat_1 @ X15 @ (k1_tarski @ X16)))
% 0.38/0.56          | ~ (v1_relat_1 @ X15))),
% 0.38/0.56      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.38/0.56  thf(t143_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ C ) =>
% 0.38/0.56       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.38/0.56         ( ?[D:$i]:
% 0.38/0.56           ( ( r2_hidden @ D @ B ) & 
% 0.38/0.56             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.38/0.56             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X19 @ (k9_relat_1 @ X20 @ X18))
% 0.38/0.56          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X20 @ X18 @ X19) @ X19) @ X20)
% 0.38/0.56          | ~ (v1_relat_1 @ X20))),
% 0.38/0.56      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | (r2_hidden @ 
% 0.38/0.56             (k4_tarski @ (sk_D_2 @ X1 @ (k1_tarski @ X0) @ X2) @ X2) @ X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         ((r2_hidden @ 
% 0.38/0.56           (k4_tarski @ (sk_D_2 @ X1 @ (k1_tarski @ X0) @ X2) @ X2) @ X1)
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | ~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['24'])).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      (((~ (v1_relat_1 @ sk_C)
% 0.38/0.56         | (r2_hidden @ 
% 0.38/0.56            (k4_tarski @ (sk_D_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B) @ sk_B) @ 
% 0.38/0.56            sk_C)))
% 0.38/0.56         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['21', '25'])).
% 0.38/0.56  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (((r2_hidden @ 
% 0.38/0.56         (k4_tarski @ (sk_D_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B) @ sk_B) @ 
% 0.38/0.56         sk_C)) <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.38/0.56      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A)))
% 0.38/0.56         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.38/0.56      inference('split', [status(esa)], ['7'])).
% 0.38/0.56  thf('30', plain,
% 0.38/0.56      (![X15 : $i, X16 : $i]:
% 0.38/0.56         (((k11_relat_1 @ X15 @ X16) = (k9_relat_1 @ X15 @ (k1_tarski @ X16)))
% 0.38/0.56          | ~ (v1_relat_1 @ X15))),
% 0.38/0.56      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X19 @ (k9_relat_1 @ X20 @ X18))
% 0.38/0.56          | (r2_hidden @ (sk_D_2 @ X20 @ X18 @ X19) @ X18)
% 0.38/0.56          | ~ (v1_relat_1 @ X20))),
% 0.38/0.56      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | (r2_hidden @ (sk_D_2 @ X1 @ (k1_tarski @ X0) @ X2) @ 
% 0.38/0.56             (k1_tarski @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         ((r2_hidden @ (sk_D_2 @ X1 @ (k1_tarski @ X0) @ X2) @ (k1_tarski @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | ~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['32'])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      (((~ (v1_relat_1 @ sk_C)
% 0.38/0.56         | (r2_hidden @ (sk_D_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.38/0.56            (k1_tarski @ sk_A))))
% 0.38/0.56         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['29', '33'])).
% 0.38/0.56  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('36', plain,
% 0.38/0.56      (((r2_hidden @ (sk_D_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.38/0.56         (k1_tarski @ sk_A)))
% 0.38/0.56         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.38/0.56      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.56  thf('37', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.38/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.56  thf('38', plain,
% 0.38/0.56      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X4 @ X2)
% 0.38/0.56          | ((X4) = (X3))
% 0.38/0.56          | ((X4) = (X0))
% 0.38/0.56          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_tarski])).
% 0.38/0.56  thf('39', plain,
% 0.38/0.56      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.38/0.56         (((X4) = (X0))
% 0.38/0.56          | ((X4) = (X3))
% 0.38/0.56          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['38'])).
% 0.38/0.56  thf('40', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['37', '39'])).
% 0.38/0.56  thf('41', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['40'])).
% 0.38/0.56  thf('42', plain,
% 0.38/0.56      ((((sk_D_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B) = (sk_A)))
% 0.38/0.56         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['36', '41'])).
% 0.38/0.56  thf('43', plain,
% 0.38/0.56      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.38/0.56         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.38/0.56      inference('demod', [status(thm)], ['28', '42'])).
% 0.38/0.56  thf('44', plain,
% 0.38/0.56      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.38/0.56         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.38/0.56      inference('split', [status(esa)], ['0'])).
% 0.38/0.56  thf('45', plain,
% 0.38/0.56      (~ ((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))) | 
% 0.38/0.56       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.38/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.56  thf('46', plain, ($false),
% 0.38/0.56      inference('sat_resolution*', [status(thm)], ['1', '19', '20', '45'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
