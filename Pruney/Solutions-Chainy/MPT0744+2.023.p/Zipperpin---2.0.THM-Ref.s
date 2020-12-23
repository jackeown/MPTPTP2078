%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NngQ0fxXAx

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:02 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 129 expanded)
%              Number of leaves         :   16 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  540 (1043 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t34_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
            <=> ( r1_ordinal1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_ordinal1])).

thf('0',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ( r1_ordinal1 @ X23 @ X24 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v3_ordinal1 @ X30 )
      | ( r1_ordinal1 @ X31 @ X30 )
      | ( r2_hidden @ X30 @ X31 )
      | ~ ( v3_ordinal1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('10',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X26 = X25 )
      | ( r2_hidden @ X26 @ X25 )
      | ~ ( r2_hidden @ X26 @ ( k1_ordinal1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('13',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('15',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r2_hidden @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( r1_ordinal1 @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','23'])).

thf('25',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('28',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v3_ordinal1 @ X30 )
      | ( r1_ordinal1 @ X31 @ X30 )
      | ( r2_hidden @ X30 @ X31 )
      | ~ ( v3_ordinal1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r2_hidden @ X26 @ ( k1_ordinal1 @ X27 ) )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_ordinal1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('37',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('42',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ~ ( v3_ordinal1 @ X24 )
      | ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_ordinal1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('43',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('47',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v3_ordinal1 @ X28 )
      | ( r2_hidden @ X29 @ X28 )
      | ( X29 = X28 )
      | ( r2_hidden @ X28 @ X29 )
      | ~ ( v3_ordinal1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('48',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('55',plain,
    ( ( ( sk_B = sk_A )
      | ~ ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r2_hidden @ X26 @ ( k1_ordinal1 @ X27 ) )
      | ( X26 != X27 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('60',plain,(
    ! [X27: $i] :
      ( r2_hidden @ X27 @ ( k1_ordinal1 @ X27 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','60'])).

thf('62',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NngQ0fxXAx
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:56:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.54/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.73  % Solved by: fo/fo7.sh
% 0.54/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.73  % done 536 iterations in 0.267s
% 0.54/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.73  % SZS output start Refutation
% 0.54/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.73  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.54/0.73  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.54/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.73  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.54/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.54/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.73  thf(t34_ordinal1, conjecture,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( v3_ordinal1 @ A ) =>
% 0.54/0.73       ( ![B:$i]:
% 0.54/0.73         ( ( v3_ordinal1 @ B ) =>
% 0.54/0.73           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.54/0.73             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.54/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.73    (~( ![A:$i]:
% 0.54/0.73        ( ( v3_ordinal1 @ A ) =>
% 0.54/0.73          ( ![B:$i]:
% 0.54/0.73            ( ( v3_ordinal1 @ B ) =>
% 0.54/0.73              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.54/0.73                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.54/0.73    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.54/0.73  thf('0', plain,
% 0.54/0.73      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.54/0.73        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('1', plain,
% 0.54/0.73      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.54/0.73       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.54/0.73      inference('split', [status(esa)], ['0'])).
% 0.54/0.73  thf(d3_tarski, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( r1_tarski @ A @ B ) <=>
% 0.54/0.73       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.54/0.73  thf('2', plain,
% 0.54/0.73      (![X3 : $i, X5 : $i]:
% 0.54/0.73         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.73  thf('3', plain,
% 0.54/0.73      (![X3 : $i, X5 : $i]:
% 0.54/0.73         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.73  thf('4', plain,
% 0.54/0.73      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.54/0.73  thf('5', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.54/0.73      inference('simplify', [status(thm)], ['4'])).
% 0.54/0.73  thf(redefinition_r1_ordinal1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.54/0.73       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.54/0.73  thf('6', plain,
% 0.54/0.73      (![X23 : $i, X24 : $i]:
% 0.54/0.73         (~ (v3_ordinal1 @ X23)
% 0.54/0.73          | ~ (v3_ordinal1 @ X24)
% 0.54/0.73          | (r1_ordinal1 @ X23 @ X24)
% 0.54/0.73          | ~ (r1_tarski @ X23 @ X24))),
% 0.54/0.73      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.54/0.73  thf('7', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['5', '6'])).
% 0.54/0.73  thf('8', plain,
% 0.54/0.73      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0))),
% 0.54/0.73      inference('simplify', [status(thm)], ['7'])).
% 0.54/0.73  thf(t26_ordinal1, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( v3_ordinal1 @ A ) =>
% 0.54/0.73       ( ![B:$i]:
% 0.54/0.73         ( ( v3_ordinal1 @ B ) =>
% 0.54/0.73           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.54/0.73  thf('9', plain,
% 0.54/0.73      (![X30 : $i, X31 : $i]:
% 0.54/0.73         (~ (v3_ordinal1 @ X30)
% 0.54/0.73          | (r1_ordinal1 @ X31 @ X30)
% 0.54/0.73          | (r2_hidden @ X30 @ X31)
% 0.54/0.73          | ~ (v3_ordinal1 @ X31))),
% 0.54/0.73      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.54/0.73  thf('10', plain,
% 0.54/0.73      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('11', plain,
% 0.54/0.73      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.54/0.73         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.54/0.73      inference('split', [status(esa)], ['10'])).
% 0.54/0.73  thf(t13_ordinal1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.54/0.73       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.54/0.73  thf('12', plain,
% 0.54/0.73      (![X25 : $i, X26 : $i]:
% 0.54/0.73         (((X26) = (X25))
% 0.54/0.73          | (r2_hidden @ X26 @ X25)
% 0.54/0.73          | ~ (r2_hidden @ X26 @ (k1_ordinal1 @ X25)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.54/0.73  thf('13', plain,
% 0.54/0.73      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.54/0.73         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['11', '12'])).
% 0.54/0.73  thf(antisymmetry_r2_hidden, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.54/0.73  thf('14', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.54/0.73      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.54/0.73  thf('15', plain,
% 0.54/0.73      (((((sk_A) = (sk_B)) | ~ (r2_hidden @ sk_B @ sk_A)))
% 0.54/0.73         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['13', '14'])).
% 0.54/0.73  thf('16', plain,
% 0.54/0.73      (((~ (v3_ordinal1 @ sk_A)
% 0.54/0.73         | (r1_ordinal1 @ sk_A @ sk_B)
% 0.54/0.73         | ~ (v3_ordinal1 @ sk_B)
% 0.54/0.73         | ((sk_A) = (sk_B)))) <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['9', '15'])).
% 0.54/0.73  thf('17', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('18', plain, ((v3_ordinal1 @ sk_B)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('19', plain,
% 0.54/0.73      ((((r1_ordinal1 @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.54/0.73         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.54/0.73      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.54/0.73  thf('20', plain,
% 0.54/0.73      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.54/0.73      inference('split', [status(esa)], ['0'])).
% 0.54/0.73  thf('21', plain,
% 0.54/0.73      ((((sk_A) = (sk_B)))
% 0.54/0.73         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.54/0.73             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['19', '20'])).
% 0.54/0.73  thf('22', plain,
% 0.54/0.73      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.54/0.73      inference('split', [status(esa)], ['0'])).
% 0.54/0.73  thf('23', plain,
% 0.54/0.73      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.54/0.73         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.54/0.73             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['21', '22'])).
% 0.54/0.73  thf('24', plain,
% 0.54/0.73      ((~ (v3_ordinal1 @ sk_A))
% 0.54/0.73         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.54/0.73             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['8', '23'])).
% 0.54/0.73  thf('25', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('26', plain,
% 0.54/0.73      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.54/0.73       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.54/0.73      inference('demod', [status(thm)], ['24', '25'])).
% 0.54/0.73  thf('27', plain,
% 0.54/0.73      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.54/0.73       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.54/0.73      inference('split', [status(esa)], ['10'])).
% 0.54/0.73  thf('28', plain,
% 0.54/0.73      (![X30 : $i, X31 : $i]:
% 0.54/0.73         (~ (v3_ordinal1 @ X30)
% 0.54/0.73          | (r1_ordinal1 @ X31 @ X30)
% 0.54/0.73          | (r2_hidden @ X30 @ X31)
% 0.54/0.73          | ~ (v3_ordinal1 @ X31))),
% 0.54/0.73      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.54/0.73  thf('29', plain,
% 0.54/0.73      (![X26 : $i, X27 : $i]:
% 0.54/0.73         ((r2_hidden @ X26 @ (k1_ordinal1 @ X27)) | ~ (r2_hidden @ X26 @ X27))),
% 0.54/0.73      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.54/0.73  thf('30', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (~ (v3_ordinal1 @ X0)
% 0.54/0.73          | (r1_ordinal1 @ X0 @ X1)
% 0.54/0.73          | ~ (v3_ordinal1 @ X1)
% 0.54/0.73          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['28', '29'])).
% 0.54/0.73  thf('31', plain,
% 0.54/0.73      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.54/0.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.54/0.73      inference('split', [status(esa)], ['0'])).
% 0.54/0.73  thf('32', plain,
% 0.54/0.73      (((~ (v3_ordinal1 @ sk_A)
% 0.54/0.73         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.54/0.73         | ~ (v3_ordinal1 @ sk_B)))
% 0.54/0.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['30', '31'])).
% 0.54/0.73  thf('33', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('34', plain, ((v3_ordinal1 @ sk_B)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('35', plain,
% 0.54/0.73      (((r1_ordinal1 @ sk_B @ sk_A))
% 0.54/0.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.54/0.73      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.54/0.73  thf('36', plain,
% 0.54/0.73      (![X23 : $i, X24 : $i]:
% 0.54/0.73         (~ (v3_ordinal1 @ X23)
% 0.54/0.73          | ~ (v3_ordinal1 @ X24)
% 0.54/0.73          | (r1_tarski @ X23 @ X24)
% 0.54/0.73          | ~ (r1_ordinal1 @ X23 @ X24))),
% 0.54/0.73      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.54/0.73  thf('37', plain,
% 0.54/0.73      ((((r1_tarski @ sk_B @ sk_A)
% 0.54/0.73         | ~ (v3_ordinal1 @ sk_A)
% 0.54/0.73         | ~ (v3_ordinal1 @ sk_B)))
% 0.54/0.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['35', '36'])).
% 0.54/0.73  thf('38', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('39', plain, ((v3_ordinal1 @ sk_B)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('40', plain,
% 0.54/0.73      (((r1_tarski @ sk_B @ sk_A))
% 0.54/0.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.54/0.73      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.54/0.73  thf('41', plain,
% 0.54/0.73      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.54/0.73      inference('split', [status(esa)], ['10'])).
% 0.54/0.73  thf('42', plain,
% 0.54/0.73      (![X23 : $i, X24 : $i]:
% 0.54/0.73         (~ (v3_ordinal1 @ X23)
% 0.54/0.73          | ~ (v3_ordinal1 @ X24)
% 0.54/0.73          | (r1_tarski @ X23 @ X24)
% 0.54/0.73          | ~ (r1_ordinal1 @ X23 @ X24))),
% 0.54/0.73      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.54/0.73  thf('43', plain,
% 0.54/0.73      ((((r1_tarski @ sk_A @ sk_B)
% 0.54/0.73         | ~ (v3_ordinal1 @ sk_B)
% 0.54/0.73         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['41', '42'])).
% 0.54/0.73  thf('44', plain, ((v3_ordinal1 @ sk_B)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('45', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('46', plain,
% 0.54/0.73      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.54/0.73      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.54/0.73  thf(t24_ordinal1, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( v3_ordinal1 @ A ) =>
% 0.54/0.73       ( ![B:$i]:
% 0.54/0.73         ( ( v3_ordinal1 @ B ) =>
% 0.54/0.73           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.54/0.73                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.54/0.73  thf('47', plain,
% 0.54/0.73      (![X28 : $i, X29 : $i]:
% 0.54/0.73         (~ (v3_ordinal1 @ X28)
% 0.54/0.73          | (r2_hidden @ X29 @ X28)
% 0.54/0.73          | ((X29) = (X28))
% 0.54/0.73          | (r2_hidden @ X28 @ X29)
% 0.54/0.73          | ~ (v3_ordinal1 @ X29))),
% 0.54/0.73      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.54/0.73  thf(t7_ordinal1, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.73  thf('48', plain,
% 0.54/0.73      (![X32 : $i, X33 : $i]:
% 0.54/0.73         (~ (r2_hidden @ X32 @ X33) | ~ (r1_tarski @ X33 @ X32))),
% 0.54/0.73      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.54/0.73  thf('49', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (~ (v3_ordinal1 @ X1)
% 0.54/0.73          | (r2_hidden @ X0 @ X1)
% 0.54/0.73          | ((X1) = (X0))
% 0.54/0.73          | ~ (v3_ordinal1 @ X0)
% 0.54/0.73          | ~ (r1_tarski @ X0 @ X1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['47', '48'])).
% 0.54/0.73  thf('50', plain,
% 0.54/0.73      (((~ (v3_ordinal1 @ sk_A)
% 0.54/0.73         | ((sk_B) = (sk_A))
% 0.54/0.73         | (r2_hidden @ sk_A @ sk_B)
% 0.54/0.73         | ~ (v3_ordinal1 @ sk_B))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['46', '49'])).
% 0.54/0.73  thf('51', plain, ((v3_ordinal1 @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('52', plain, ((v3_ordinal1 @ sk_B)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('53', plain,
% 0.54/0.73      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B)))
% 0.54/0.73         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.54/0.73      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.54/0.73  thf('54', plain,
% 0.54/0.73      (![X32 : $i, X33 : $i]:
% 0.54/0.73         (~ (r2_hidden @ X32 @ X33) | ~ (r1_tarski @ X33 @ X32))),
% 0.54/0.73      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.54/0.73  thf('55', plain,
% 0.54/0.73      (((((sk_B) = (sk_A)) | ~ (r1_tarski @ sk_B @ sk_A)))
% 0.54/0.73         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.73  thf('56', plain,
% 0.54/0.73      ((((sk_B) = (sk_A)))
% 0.54/0.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.54/0.73             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['40', '55'])).
% 0.54/0.73  thf('57', plain,
% 0.54/0.73      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.54/0.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.54/0.73      inference('split', [status(esa)], ['0'])).
% 0.54/0.73  thf('58', plain,
% 0.54/0.73      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.54/0.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.54/0.73             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['56', '57'])).
% 0.54/0.73  thf('59', plain,
% 0.54/0.73      (![X26 : $i, X27 : $i]:
% 0.54/0.73         ((r2_hidden @ X26 @ (k1_ordinal1 @ X27)) | ((X26) != (X27)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.54/0.73  thf('60', plain, (![X27 : $i]: (r2_hidden @ X27 @ (k1_ordinal1 @ X27))),
% 0.54/0.73      inference('simplify', [status(thm)], ['59'])).
% 0.54/0.73  thf('61', plain,
% 0.54/0.73      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.54/0.73       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.54/0.73      inference('demod', [status(thm)], ['58', '60'])).
% 0.54/0.73  thf('62', plain, ($false),
% 0.54/0.73      inference('sat_resolution*', [status(thm)], ['1', '26', '27', '61'])).
% 0.54/0.73  
% 0.54/0.73  % SZS output end Refutation
% 0.54/0.73  
% 0.54/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
