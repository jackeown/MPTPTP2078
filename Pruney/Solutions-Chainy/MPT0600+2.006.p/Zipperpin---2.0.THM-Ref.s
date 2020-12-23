%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rUcopP9dId

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:41 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 106 expanded)
%              Number of leaves         :   19 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  598 (1024 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X39: $i,X40: $i] :
      ( ( ( k11_relat_1 @ X39 @ X40 )
        = ( k9_relat_1 @ X39 @ ( k1_tarski @ X40 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
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

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ~ ( r2_hidden @ ( k4_tarski @ X41 @ X43 ) @ X44 )
      | ~ ( r2_hidden @ X41 @ ( k1_relat_1 @ X44 ) )
      | ( r2_hidden @ X43 @ ( k9_relat_1 @ X44 @ X42 ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ( r2_hidden @ sk_B @ ( k9_relat_1 @ sk_C @ X0 ) )
        | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('13',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X45 @ X46 ) @ X47 )
      | ( r2_hidden @ X45 @ ( k1_relat_1 @ X47 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ ( k9_relat_1 @ sk_C @ X0 ) )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['10','11','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_B @ ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,
    ( ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['2','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
   <= ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf('25',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('26',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k11_relat_1 @ X39 @ X40 )
        = ( k9_relat_1 @ X39 @ ( k1_tarski @ X40 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('27',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X43 @ ( k9_relat_1 @ X44 @ X42 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X44 @ X42 @ X43 ) @ X43 ) @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ) @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('33',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k11_relat_1 @ X39 @ X40 )
        = ( k9_relat_1 @ X39 @ ( k1_tarski @ X40 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('34',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X43 @ ( k9_relat_1 @ X44 @ X42 ) )
      | ( r2_hidden @ ( sk_D_1 @ X44 @ X42 @ X43 ) @ X42 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_tarski @ X0 ) @ X2 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('41',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('42',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( sk_D_1 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B )
      = sk_A )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31','45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k11_relat_1 @ sk_C @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rUcopP9dId
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:34:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 134 iterations in 0.045s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.55  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.37/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.37/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.55  thf(t204_relat_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ C ) =>
% 0.37/0.55       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.37/0.55         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.55        ( ( v1_relat_1 @ C ) =>
% 0.37/0.55          ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.37/0.55            ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t204_relat_1])).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      ((~ (r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))
% 0.37/0.55        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (~ ((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))) | 
% 0.37/0.55       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf(d16_relat_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (![X39 : $i, X40 : $i]:
% 0.37/0.55         (((k11_relat_1 @ X39 @ X40) = (k9_relat_1 @ X39 @ (k1_tarski @ X40)))
% 0.37/0.55          | ~ (v1_relat_1 @ X39))),
% 0.37/0.55      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.37/0.55  thf(t69_enumset1, axiom,
% 0.37/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.55  thf('3', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.55  thf(d2_tarski, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.37/0.55       ( ![D:$i]:
% 0.37/0.55         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         (((X1) != (X0))
% 0.37/0.55          | (r2_hidden @ X1 @ X2)
% 0.37/0.55          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_tarski])).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.37/0.55      inference('simplify', [status(thm)], ['4'])).
% 0.37/0.55  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['3', '5'])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))
% 0.37/0.55        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.37/0.55         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.37/0.55      inference('split', [status(esa)], ['7'])).
% 0.37/0.55  thf(t143_relat_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ C ) =>
% 0.37/0.55       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.37/0.55         ( ?[D:$i]:
% 0.37/0.55           ( ( r2_hidden @ D @ B ) & 
% 0.37/0.55             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.37/0.55             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X41 @ X42)
% 0.37/0.55          | ~ (r2_hidden @ (k4_tarski @ X41 @ X43) @ X44)
% 0.37/0.55          | ~ (r2_hidden @ X41 @ (k1_relat_1 @ X44))
% 0.37/0.55          | (r2_hidden @ X43 @ (k9_relat_1 @ X44 @ X42))
% 0.37/0.55          | ~ (v1_relat_1 @ X44))),
% 0.37/0.55      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      ((![X0 : $i]:
% 0.37/0.55          (~ (v1_relat_1 @ sk_C)
% 0.37/0.55           | (r2_hidden @ sk_B @ (k9_relat_1 @ sk_C @ X0))
% 0.37/0.55           | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))
% 0.37/0.55           | ~ (r2_hidden @ sk_A @ X0)))
% 0.37/0.55         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.55  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.37/0.55         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.37/0.55      inference('split', [status(esa)], ['7'])).
% 0.37/0.55  thf(t20_relat_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ C ) =>
% 0.37/0.55       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.37/0.55         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.37/0.55           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.37/0.55         (~ (r2_hidden @ (k4_tarski @ X45 @ X46) @ X47)
% 0.37/0.55          | (r2_hidden @ X45 @ (k1_relat_1 @ X47))
% 0.37/0.55          | ~ (v1_relat_1 @ X47))),
% 0.37/0.55      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      (((~ (v1_relat_1 @ sk_C) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))))
% 0.37/0.55         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.55  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))
% 0.37/0.55         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.37/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      ((![X0 : $i]:
% 0.37/0.55          ((r2_hidden @ sk_B @ (k9_relat_1 @ sk_C @ X0))
% 0.37/0.55           | ~ (r2_hidden @ sk_A @ X0)))
% 0.37/0.55         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.37/0.55      inference('demod', [status(thm)], ['10', '11', '16'])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      (((r2_hidden @ sk_B @ (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A))))
% 0.37/0.55         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['6', '17'])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      ((((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))
% 0.37/0.55         | ~ (v1_relat_1 @ sk_C)))
% 0.37/0.55         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['2', '18'])).
% 0.37/0.55  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A)))
% 0.37/0.55         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.37/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      ((~ (r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A)))
% 0.37/0.55         <= (~ ((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))) | 
% 0.37/0.55       ~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))) | 
% 0.37/0.55       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.37/0.55      inference('split', [status(esa)], ['7'])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A)))
% 0.37/0.55         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.37/0.55      inference('split', [status(esa)], ['7'])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (![X39 : $i, X40 : $i]:
% 0.37/0.55         (((k11_relat_1 @ X39 @ X40) = (k9_relat_1 @ X39 @ (k1_tarski @ X40)))
% 0.37/0.55          | ~ (v1_relat_1 @ X39))),
% 0.37/0.55      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X43 @ (k9_relat_1 @ X44 @ X42))
% 0.37/0.55          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X44 @ X42 @ X43) @ X43) @ X44)
% 0.37/0.55          | ~ (v1_relat_1 @ X44))),
% 0.37/0.55      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0))
% 0.37/0.55          | ~ (v1_relat_1 @ X1)
% 0.37/0.55          | ~ (v1_relat_1 @ X1)
% 0.37/0.55          | (r2_hidden @ 
% 0.37/0.55             (k4_tarski @ (sk_D_1 @ X1 @ (k1_tarski @ X0) @ X2) @ X2) @ X1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         ((r2_hidden @ 
% 0.37/0.55           (k4_tarski @ (sk_D_1 @ X1 @ (k1_tarski @ X0) @ X2) @ X2) @ X1)
% 0.37/0.55          | ~ (v1_relat_1 @ X1)
% 0.37/0.55          | ~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['28'])).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      (((~ (v1_relat_1 @ sk_C)
% 0.37/0.55         | (r2_hidden @ 
% 0.37/0.55            (k4_tarski @ (sk_D_1 @ sk_C @ (k1_tarski @ sk_A) @ sk_B) @ sk_B) @ 
% 0.37/0.55            sk_C)))
% 0.37/0.55         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['25', '29'])).
% 0.37/0.55  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A)))
% 0.37/0.55         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.37/0.55      inference('split', [status(esa)], ['7'])).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      (![X39 : $i, X40 : $i]:
% 0.37/0.55         (((k11_relat_1 @ X39 @ X40) = (k9_relat_1 @ X39 @ (k1_tarski @ X40)))
% 0.37/0.55          | ~ (v1_relat_1 @ X39))),
% 0.37/0.55      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X43 @ (k9_relat_1 @ X44 @ X42))
% 0.37/0.55          | (r2_hidden @ (sk_D_1 @ X44 @ X42 @ X43) @ X42)
% 0.37/0.55          | ~ (v1_relat_1 @ X44))),
% 0.37/0.55      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0))
% 0.37/0.55          | ~ (v1_relat_1 @ X1)
% 0.37/0.55          | ~ (v1_relat_1 @ X1)
% 0.37/0.55          | (r2_hidden @ (sk_D_1 @ X1 @ (k1_tarski @ X0) @ X2) @ 
% 0.37/0.55             (k1_tarski @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         ((r2_hidden @ (sk_D_1 @ X1 @ (k1_tarski @ X0) @ X2) @ (k1_tarski @ X0))
% 0.37/0.55          | ~ (v1_relat_1 @ X1)
% 0.37/0.55          | ~ (r2_hidden @ X2 @ (k11_relat_1 @ X1 @ X0)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['35'])).
% 0.37/0.55  thf('37', plain,
% 0.37/0.55      (((~ (v1_relat_1 @ sk_C)
% 0.37/0.55         | (r2_hidden @ (sk_D_1 @ sk_C @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.37/0.55            (k1_tarski @ sk_A))))
% 0.37/0.55         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['32', '36'])).
% 0.37/0.55  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('39', plain,
% 0.37/0.55      (((r2_hidden @ (sk_D_1 @ sk_C @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.37/0.55         (k1_tarski @ sk_A)))
% 0.37/0.55         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.55  thf('40', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X4 @ X2)
% 0.37/0.55          | ((X4) = (X3))
% 0.37/0.55          | ((X4) = (X0))
% 0.37/0.55          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d2_tarski])).
% 0.37/0.55  thf('42', plain,
% 0.37/0.55      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.37/0.55         (((X4) = (X0))
% 0.37/0.55          | ((X4) = (X3))
% 0.37/0.55          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['41'])).
% 0.37/0.55  thf('43', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['40', '42'])).
% 0.37/0.55  thf('44', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['43'])).
% 0.37/0.55  thf('45', plain,
% 0.37/0.55      ((((sk_D_1 @ sk_C @ (k1_tarski @ sk_A) @ sk_B) = (sk_A)))
% 0.37/0.55         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['39', '44'])).
% 0.37/0.55  thf('46', plain,
% 0.37/0.55      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.37/0.55         <= (((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))))),
% 0.37/0.55      inference('demod', [status(thm)], ['30', '31', '45'])).
% 0.37/0.55  thf('47', plain,
% 0.37/0.55      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.37/0.55         <= (~ ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('48', plain,
% 0.37/0.55      (~ ((r2_hidden @ sk_B @ (k11_relat_1 @ sk_C @ sk_A))) | 
% 0.37/0.55       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.37/0.55  thf('49', plain, ($false),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['1', '23', '24', '48'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
