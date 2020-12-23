%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bIzi8woWGp

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:06 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 119 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  528 ( 886 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('4',plain,(
    ! [X43: $i] :
      ( ( k1_ordinal1 @ X43 )
      = ( k2_xboole_0 @ X43 @ ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('6',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_tarski @ X37 @ ( k3_tarski @ X38 ) )
      | ~ ( r2_hidden @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('10',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ( r1_tarski @ sk_A @ ( k3_tarski @ ( k1_tarski @ sk_B_1 ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('11',plain,(
    ! [X41: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('12',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X44 @ X45 )
      | ( r1_tarski @ X44 @ X45 )
      | ~ ( v1_ordinal1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('14',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('16',plain,(
    ! [X42: $i] :
      ( ( v1_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('17',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v3_ordinal1 @ X47 )
      | ~ ( v3_ordinal1 @ X48 )
      | ( r1_ordinal1 @ X47 @ X48 )
      | ~ ( r1_tarski @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('21',plain,
    ( ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X43: $i] :
      ( ( k1_ordinal1 @ X43 )
      = ( k2_xboole_0 @ X43 @ ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('32',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v3_ordinal1 @ X47 )
      | ~ ( v3_ordinal1 @ X48 )
      | ( r1_tarski @ X47 @ X48 )
      | ~ ( r1_ordinal1 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('33',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('37',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_xboole_0 @ X6 @ X8 )
      | ( X6 = X8 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('38',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r2_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('39',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v3_ordinal1 @ X50 )
      | ( r2_hidden @ X51 @ X50 )
      | ~ ( r2_xboole_0 @ X51 @ X50 )
      | ~ ( v1_ordinal1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('40',plain,
    ( ( ( sk_A = sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X42: $i] :
      ( ( v1_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('43',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['40','43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( sk_A = sk_B_1 )
        | ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      | ( sk_A = sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['30','48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ( sk_A = sk_B_1 )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('54',plain,(
    ! [X49: $i] :
      ( r2_hidden @ X49 @ ( k1_ordinal1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('55',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bIzi8woWGp
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:39:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 251 iterations in 0.090s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.36/0.54  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.36/0.54  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.36/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.36/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.36/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.54  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.36/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.54  thf(t34_ordinal1, conjecture,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v3_ordinal1 @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( v3_ordinal1 @ B ) =>
% 0.36/0.54           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.36/0.54             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i]:
% 0.36/0.54        ( ( v3_ordinal1 @ A ) =>
% 0.36/0.54          ( ![B:$i]:
% 0.36/0.54            ( ( v3_ordinal1 @ B ) =>
% 0.36/0.54              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.36/0.54                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)
% 0.36/0.54        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.36/0.54       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.36/0.54      inference('split', [status(esa)], ['0'])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (((r1_ordinal1 @ sk_A @ sk_B_1)
% 0.36/0.54        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.36/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.54      inference('split', [status(esa)], ['2'])).
% 0.36/0.54  thf(d1_ordinal1, axiom,
% 0.36/0.54    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (![X43 : $i]:
% 0.36/0.54         ((k1_ordinal1 @ X43) = (k2_xboole_0 @ X43 @ (k1_tarski @ X43)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.36/0.54  thf(d3_xboole_0, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.36/0.54       ( ![D:$i]:
% 0.36/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.54           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X4 @ X2)
% 0.36/0.54          | (r2_hidden @ X4 @ X3)
% 0.36/0.54          | (r2_hidden @ X4 @ X1)
% 0.36/0.54          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.36/0.54         ((r2_hidden @ X4 @ X1)
% 0.36/0.54          | (r2_hidden @ X4 @ X3)
% 0.36/0.54          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['5'])).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.36/0.54          | (r2_hidden @ X1 @ X0)
% 0.36/0.54          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['4', '6'])).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))
% 0.36/0.54         | (r2_hidden @ sk_A @ sk_B_1)))
% 0.36/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['3', '7'])).
% 0.36/0.54  thf(l49_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (![X37 : $i, X38 : $i]:
% 0.36/0.54         ((r1_tarski @ X37 @ (k3_tarski @ X38)) | ~ (r2_hidden @ X37 @ X38))),
% 0.36/0.54      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.36/0.54  thf('10', plain,
% 0.36/0.54      ((((r2_hidden @ sk_A @ sk_B_1)
% 0.36/0.54         | (r1_tarski @ sk_A @ (k3_tarski @ (k1_tarski @ sk_B_1)))))
% 0.36/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.54  thf(t31_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.36/0.54  thf('11', plain, (![X41 : $i]: ((k3_tarski @ (k1_tarski @ X41)) = (X41))),
% 0.36/0.54      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      ((((r2_hidden @ sk_A @ sk_B_1) | (r1_tarski @ sk_A @ sk_B_1)))
% 0.36/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.54  thf(d2_ordinal1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_ordinal1 @ A ) <=>
% 0.36/0.54       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (![X44 : $i, X45 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X44 @ X45)
% 0.36/0.54          | (r1_tarski @ X44 @ X45)
% 0.36/0.54          | ~ (v1_ordinal1 @ X45))),
% 0.36/0.54      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      ((((r1_tarski @ sk_A @ sk_B_1)
% 0.36/0.54         | ~ (v1_ordinal1 @ sk_B_1)
% 0.36/0.54         | (r1_tarski @ sk_A @ sk_B_1)))
% 0.36/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.54  thf('15', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(cc1_ordinal1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      (![X42 : $i]: ((v1_ordinal1 @ X42) | ~ (v3_ordinal1 @ X42))),
% 0.36/0.54      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.36/0.54  thf('17', plain, ((v1_ordinal1 @ sk_B_1)),
% 0.36/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      ((((r1_tarski @ sk_A @ sk_B_1) | (r1_tarski @ sk_A @ sk_B_1)))
% 0.36/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.54      inference('demod', [status(thm)], ['14', '17'])).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (((r1_tarski @ sk_A @ sk_B_1))
% 0.36/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.54      inference('simplify', [status(thm)], ['18'])).
% 0.36/0.54  thf(redefinition_r1_ordinal1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.36/0.54       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      (![X47 : $i, X48 : $i]:
% 0.36/0.54         (~ (v3_ordinal1 @ X47)
% 0.36/0.54          | ~ (v3_ordinal1 @ X48)
% 0.36/0.54          | (r1_ordinal1 @ X47 @ X48)
% 0.36/0.54          | ~ (r1_tarski @ X47 @ X48))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      ((((r1_ordinal1 @ sk_A @ sk_B_1)
% 0.36/0.54         | ~ (v3_ordinal1 @ sk_B_1)
% 0.36/0.54         | ~ (v3_ordinal1 @ sk_A)))
% 0.36/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.54  thf('22', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('23', plain, ((v3_ordinal1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      (((r1_ordinal1 @ sk_A @ sk_B_1))
% 0.36/0.54         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.54      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.36/0.54      inference('split', [status(esa)], ['0'])).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.36/0.54       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.36/0.54       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.36/0.54      inference('split', [status(esa)], ['2'])).
% 0.36/0.54  thf(t69_enumset1, axiom,
% 0.36/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.54  thf('28', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.36/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.54  thf('29', plain,
% 0.36/0.54      (![X43 : $i]:
% 0.36/0.54         ((k1_ordinal1 @ X43) = (k2_xboole_0 @ X43 @ (k1_tarski @ X43)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.36/0.54  thf('30', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['28', '29'])).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      (((r1_ordinal1 @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.36/0.54      inference('split', [status(esa)], ['2'])).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (![X47 : $i, X48 : $i]:
% 0.36/0.54         (~ (v3_ordinal1 @ X47)
% 0.36/0.54          | ~ (v3_ordinal1 @ X48)
% 0.36/0.54          | (r1_tarski @ X47 @ X48)
% 0.36/0.54          | ~ (r1_ordinal1 @ X47 @ X48))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      ((((r1_tarski @ sk_A @ sk_B_1)
% 0.36/0.54         | ~ (v3_ordinal1 @ sk_B_1)
% 0.36/0.54         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.54  thf('34', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('35', plain, ((v3_ordinal1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('36', plain,
% 0.36/0.54      (((r1_tarski @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.36/0.54      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.36/0.54  thf(d8_xboole_0, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.36/0.54       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.36/0.54  thf('37', plain,
% 0.36/0.54      (![X6 : $i, X8 : $i]:
% 0.36/0.54         ((r2_xboole_0 @ X6 @ X8) | ((X6) = (X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.36/0.54      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.36/0.54  thf('38', plain,
% 0.36/0.54      (((((sk_A) = (sk_B_1)) | (r2_xboole_0 @ sk_A @ sk_B_1)))
% 0.36/0.54         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.54  thf(t21_ordinal1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_ordinal1 @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( v3_ordinal1 @ B ) =>
% 0.36/0.54           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.36/0.54  thf('39', plain,
% 0.36/0.54      (![X50 : $i, X51 : $i]:
% 0.36/0.54         (~ (v3_ordinal1 @ X50)
% 0.36/0.54          | (r2_hidden @ X51 @ X50)
% 0.36/0.54          | ~ (r2_xboole_0 @ X51 @ X50)
% 0.36/0.54          | ~ (v1_ordinal1 @ X51))),
% 0.36/0.54      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.36/0.54  thf('40', plain,
% 0.36/0.54      (((((sk_A) = (sk_B_1))
% 0.36/0.54         | ~ (v1_ordinal1 @ sk_A)
% 0.36/0.54         | (r2_hidden @ sk_A @ sk_B_1)
% 0.36/0.54         | ~ (v3_ordinal1 @ sk_B_1))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.54  thf('41', plain, ((v3_ordinal1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('42', plain,
% 0.36/0.54      (![X42 : $i]: ((v1_ordinal1 @ X42) | ~ (v3_ordinal1 @ X42))),
% 0.36/0.54      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.36/0.54  thf('43', plain, ((v1_ordinal1 @ sk_A)),
% 0.36/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.36/0.54  thf('44', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('45', plain,
% 0.36/0.54      (((((sk_A) = (sk_B_1)) | (r2_hidden @ sk_A @ sk_B_1)))
% 0.36/0.54         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.36/0.54      inference('demod', [status(thm)], ['40', '43', '44'])).
% 0.36/0.54  thf('46', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X0 @ X3)
% 0.36/0.54          | (r2_hidden @ X0 @ X2)
% 0.36/0.54          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.36/0.54  thf('47', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.36/0.54         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.36/0.54      inference('simplify', [status(thm)], ['46'])).
% 0.36/0.54  thf('48', plain,
% 0.36/0.54      ((![X0 : $i]:
% 0.36/0.54          (((sk_A) = (sk_B_1))
% 0.36/0.54           | (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B_1 @ X0))))
% 0.36/0.54         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['45', '47'])).
% 0.36/0.54  thf('49', plain,
% 0.36/0.54      ((((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)) | ((sk_A) = (sk_B_1))))
% 0.36/0.54         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['30', '48'])).
% 0.36/0.54  thf('50', plain,
% 0.36/0.54      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.36/0.54         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.54      inference('split', [status(esa)], ['0'])).
% 0.36/0.54  thf('51', plain,
% 0.36/0.54      ((((sk_A) = (sk_B_1)))
% 0.36/0.54         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 0.36/0.54             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.54  thf('52', plain,
% 0.36/0.54      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.36/0.54         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.36/0.54      inference('split', [status(esa)], ['0'])).
% 0.36/0.54  thf('53', plain,
% 0.36/0.54      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.36/0.54         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 0.36/0.54             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['51', '52'])).
% 0.36/0.54  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.36/0.54  thf('54', plain, (![X49 : $i]: (r2_hidden @ X49 @ (k1_ordinal1 @ X49))),
% 0.36/0.54      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.36/0.54  thf('55', plain,
% 0.36/0.54      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.36/0.54       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.36/0.54      inference('demod', [status(thm)], ['53', '54'])).
% 0.36/0.54  thf('56', plain, ($false),
% 0.36/0.54      inference('sat_resolution*', [status(thm)], ['1', '26', '27', '55'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
