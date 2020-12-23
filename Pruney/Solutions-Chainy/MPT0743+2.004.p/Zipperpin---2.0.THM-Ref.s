%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7iukjCDSor

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:52 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 366 expanded)
%              Number of leaves         :   15 ( 107 expanded)
%              Depth                    :   20
%              Number of atoms          :  566 (3004 expanded)
%              Number of equality atoms :   13 (  30 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t33_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ B )
            <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_ordinal1])).

thf('0',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('6',plain,(
    ! [X27: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X27 ) )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('7',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v3_ordinal1 @ X20 )
      | ~ ( v3_ordinal1 @ X21 )
      | ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_ordinal1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('9',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_ordinal1 @ X25 )
      | ( r1_ordinal1 @ X26 @ X25 )
      | ( r2_hidden @ X25 @ X26 )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ ( k1_ordinal1 @ X24 ) )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v3_ordinal1 @ X20 )
      | ~ ( v3_ordinal1 @ X21 )
      | ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_ordinal1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('25',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_ordinal1 @ X25 )
      | ( r1_ordinal1 @ X26 @ X25 )
      | ( r2_hidden @ X25 @ X26 )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('31',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v3_ordinal1 @ X20 )
      | ~ ( v3_ordinal1 @ X21 )
      | ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_ordinal1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('36',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,
    ( ( ~ ( r1_tarski @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','41'])).

thf('43',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('44',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ ( k1_ordinal1 @ X24 ) )
      | ( X23 != X24 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('46',plain,(
    ! [X24: $i] :
      ( r2_hidden @ X24 @ ( k1_ordinal1 @ X24 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('48',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','49','50'])).

thf('52',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','51'])).

thf('53',plain,(
    ! [X27: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X27 ) )
      | ~ ( v3_ordinal1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('54',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_ordinal1 @ X25 )
      | ( r1_ordinal1 @ X26 @ X25 )
      | ( r2_hidden @ X25 @ X26 )
      | ~ ( v3_ordinal1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('55',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23 = X22 )
      | ( r2_hidden @ X23 @ X22 )
      | ~ ( r2_hidden @ X23 @ ( k1_ordinal1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('59',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','49'])).

thf('60',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('67',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','49','50'])).

thf('69',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['67','68'])).

thf('70',plain,(
    sk_B = sk_A ),
    inference(clc,[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('72',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['52','70','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7iukjCDSor
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.06/1.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.06/1.29  % Solved by: fo/fo7.sh
% 1.06/1.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.29  % done 2147 iterations in 0.838s
% 1.06/1.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.06/1.29  % SZS output start Refutation
% 1.06/1.29  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 1.06/1.29  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.29  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 1.06/1.29  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.29  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 1.06/1.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.29  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.29  thf(t33_ordinal1, conjecture,
% 1.06/1.29    (![A:$i]:
% 1.06/1.29     ( ( v3_ordinal1 @ A ) =>
% 1.06/1.29       ( ![B:$i]:
% 1.06/1.29         ( ( v3_ordinal1 @ B ) =>
% 1.06/1.29           ( ( r2_hidden @ A @ B ) <=>
% 1.06/1.29             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 1.06/1.29  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.29    (~( ![A:$i]:
% 1.06/1.29        ( ( v3_ordinal1 @ A ) =>
% 1.06/1.29          ( ![B:$i]:
% 1.06/1.29            ( ( v3_ordinal1 @ B ) =>
% 1.06/1.29              ( ( r2_hidden @ A @ B ) <=>
% 1.06/1.29                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 1.06/1.29    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 1.06/1.29  thf('0', plain,
% 1.06/1.29      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('1', plain,
% 1.06/1.29      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.06/1.29      inference('split', [status(esa)], ['0'])).
% 1.06/1.29  thf(t7_ordinal1, axiom,
% 1.06/1.29    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.06/1.29  thf('2', plain,
% 1.06/1.29      (![X28 : $i, X29 : $i]:
% 1.06/1.29         (~ (r2_hidden @ X28 @ X29) | ~ (r1_tarski @ X29 @ X28))),
% 1.06/1.29      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.06/1.29  thf('3', plain,
% 1.06/1.29      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['1', '2'])).
% 1.06/1.29  thf('4', plain,
% 1.06/1.29      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 1.06/1.29        | ~ (r2_hidden @ sk_A @ sk_B))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('5', plain,
% 1.06/1.29      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 1.06/1.29       ~ ((r2_hidden @ sk_A @ sk_B))),
% 1.06/1.29      inference('split', [status(esa)], ['4'])).
% 1.06/1.29  thf(t29_ordinal1, axiom,
% 1.06/1.29    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 1.06/1.29  thf('6', plain,
% 1.06/1.29      (![X27 : $i]:
% 1.06/1.29         ((v3_ordinal1 @ (k1_ordinal1 @ X27)) | ~ (v3_ordinal1 @ X27))),
% 1.06/1.29      inference('cnf', [status(esa)], [t29_ordinal1])).
% 1.06/1.29  thf('7', plain,
% 1.06/1.29      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 1.06/1.29         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.06/1.29      inference('split', [status(esa)], ['0'])).
% 1.06/1.29  thf(redefinition_r1_ordinal1, axiom,
% 1.06/1.29    (![A:$i,B:$i]:
% 1.06/1.29     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 1.06/1.29       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 1.06/1.29  thf('8', plain,
% 1.06/1.29      (![X20 : $i, X21 : $i]:
% 1.06/1.29         (~ (v3_ordinal1 @ X20)
% 1.06/1.29          | ~ (v3_ordinal1 @ X21)
% 1.06/1.29          | (r1_tarski @ X20 @ X21)
% 1.06/1.29          | ~ (r1_ordinal1 @ X20 @ X21))),
% 1.06/1.29      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.06/1.29  thf('9', plain,
% 1.06/1.29      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 1.06/1.29         | ~ (v3_ordinal1 @ sk_B)
% 1.06/1.29         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 1.06/1.29         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['7', '8'])).
% 1.06/1.29  thf('10', plain, ((v3_ordinal1 @ sk_B)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('11', plain,
% 1.06/1.29      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 1.06/1.29         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 1.06/1.29         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.06/1.29      inference('demod', [status(thm)], ['9', '10'])).
% 1.06/1.29  thf('12', plain,
% 1.06/1.29      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 1.06/1.29         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['6', '11'])).
% 1.06/1.29  thf('13', plain, ((v3_ordinal1 @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('14', plain,
% 1.06/1.29      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 1.06/1.29         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.06/1.29      inference('demod', [status(thm)], ['12', '13'])).
% 1.06/1.29  thf(t26_ordinal1, axiom,
% 1.06/1.29    (![A:$i]:
% 1.06/1.29     ( ( v3_ordinal1 @ A ) =>
% 1.06/1.29       ( ![B:$i]:
% 1.06/1.29         ( ( v3_ordinal1 @ B ) =>
% 1.06/1.29           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 1.06/1.29  thf('15', plain,
% 1.06/1.29      (![X25 : $i, X26 : $i]:
% 1.06/1.29         (~ (v3_ordinal1 @ X25)
% 1.06/1.29          | (r1_ordinal1 @ X26 @ X25)
% 1.06/1.29          | (r2_hidden @ X25 @ X26)
% 1.06/1.29          | ~ (v3_ordinal1 @ X26))),
% 1.06/1.29      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.06/1.29  thf(t13_ordinal1, axiom,
% 1.06/1.29    (![A:$i,B:$i]:
% 1.06/1.29     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 1.06/1.29       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 1.06/1.29  thf('16', plain,
% 1.06/1.29      (![X23 : $i, X24 : $i]:
% 1.06/1.29         ((r2_hidden @ X23 @ (k1_ordinal1 @ X24)) | ~ (r2_hidden @ X23 @ X24))),
% 1.06/1.29      inference('cnf', [status(esa)], [t13_ordinal1])).
% 1.06/1.29  thf('17', plain,
% 1.06/1.29      (![X0 : $i, X1 : $i]:
% 1.06/1.29         (~ (v3_ordinal1 @ X0)
% 1.06/1.29          | (r1_ordinal1 @ X0 @ X1)
% 1.06/1.29          | ~ (v3_ordinal1 @ X1)
% 1.06/1.29          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['15', '16'])).
% 1.06/1.29  thf('18', plain,
% 1.06/1.29      (![X28 : $i, X29 : $i]:
% 1.06/1.29         (~ (r2_hidden @ X28 @ X29) | ~ (r1_tarski @ X29 @ X28))),
% 1.06/1.29      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.06/1.29  thf('19', plain,
% 1.06/1.29      (![X0 : $i, X1 : $i]:
% 1.06/1.29         (~ (v3_ordinal1 @ X1)
% 1.06/1.29          | (r1_ordinal1 @ X0 @ X1)
% 1.06/1.29          | ~ (v3_ordinal1 @ X0)
% 1.06/1.29          | ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X1))),
% 1.06/1.29      inference('sup-', [status(thm)], ['17', '18'])).
% 1.06/1.29  thf('20', plain,
% 1.06/1.29      (((~ (v3_ordinal1 @ sk_A)
% 1.06/1.29         | (r1_ordinal1 @ sk_A @ sk_B)
% 1.06/1.29         | ~ (v3_ordinal1 @ sk_B)))
% 1.06/1.29         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['14', '19'])).
% 1.06/1.29  thf('21', plain, ((v3_ordinal1 @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('22', plain, ((v3_ordinal1 @ sk_B)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('23', plain,
% 1.06/1.29      (((r1_ordinal1 @ sk_A @ sk_B))
% 1.06/1.29         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.06/1.29      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.06/1.29  thf('24', plain,
% 1.06/1.29      (![X20 : $i, X21 : $i]:
% 1.06/1.29         (~ (v3_ordinal1 @ X20)
% 1.06/1.29          | ~ (v3_ordinal1 @ X21)
% 1.06/1.29          | (r1_tarski @ X20 @ X21)
% 1.06/1.29          | ~ (r1_ordinal1 @ X20 @ X21))),
% 1.06/1.29      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.06/1.29  thf('25', plain,
% 1.06/1.29      ((((r1_tarski @ sk_A @ sk_B)
% 1.06/1.29         | ~ (v3_ordinal1 @ sk_B)
% 1.06/1.29         | ~ (v3_ordinal1 @ sk_A)))
% 1.06/1.29         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['23', '24'])).
% 1.06/1.29  thf('26', plain, ((v3_ordinal1 @ sk_B)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('28', plain,
% 1.06/1.29      (((r1_tarski @ sk_A @ sk_B))
% 1.06/1.29         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.06/1.29      inference('demod', [status(thm)], ['25', '26', '27'])).
% 1.06/1.29  thf('29', plain,
% 1.06/1.29      (![X25 : $i, X26 : $i]:
% 1.06/1.29         (~ (v3_ordinal1 @ X25)
% 1.06/1.29          | (r1_ordinal1 @ X26 @ X25)
% 1.06/1.29          | (r2_hidden @ X25 @ X26)
% 1.06/1.29          | ~ (v3_ordinal1 @ X26))),
% 1.06/1.29      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.06/1.29  thf('30', plain,
% 1.06/1.29      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.06/1.29      inference('split', [status(esa)], ['4'])).
% 1.06/1.29  thf('31', plain,
% 1.06/1.29      (((~ (v3_ordinal1 @ sk_B)
% 1.06/1.29         | (r1_ordinal1 @ sk_B @ sk_A)
% 1.06/1.29         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['29', '30'])).
% 1.06/1.29  thf('32', plain, ((v3_ordinal1 @ sk_B)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('33', plain, ((v3_ordinal1 @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('34', plain,
% 1.06/1.29      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.06/1.29      inference('demod', [status(thm)], ['31', '32', '33'])).
% 1.06/1.29  thf('35', plain,
% 1.06/1.29      (![X20 : $i, X21 : $i]:
% 1.06/1.29         (~ (v3_ordinal1 @ X20)
% 1.06/1.29          | ~ (v3_ordinal1 @ X21)
% 1.06/1.29          | (r1_tarski @ X20 @ X21)
% 1.06/1.29          | ~ (r1_ordinal1 @ X20 @ X21))),
% 1.06/1.29      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.06/1.29  thf('36', plain,
% 1.06/1.29      ((((r1_tarski @ sk_B @ sk_A)
% 1.06/1.29         | ~ (v3_ordinal1 @ sk_A)
% 1.06/1.29         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['34', '35'])).
% 1.06/1.29  thf('37', plain, ((v3_ordinal1 @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('38', plain, ((v3_ordinal1 @ sk_B)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('39', plain,
% 1.06/1.29      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.06/1.29      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.06/1.29  thf(d10_xboole_0, axiom,
% 1.06/1.29    (![A:$i,B:$i]:
% 1.06/1.29     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.06/1.29  thf('40', plain,
% 1.06/1.29      (![X8 : $i, X10 : $i]:
% 1.06/1.29         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 1.06/1.29      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.06/1.29  thf('41', plain,
% 1.06/1.29      (((~ (r1_tarski @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 1.06/1.29         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['39', '40'])).
% 1.06/1.29  thf('42', plain,
% 1.06/1.29      ((((sk_A) = (sk_B)))
% 1.06/1.29         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 1.06/1.29             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['28', '41'])).
% 1.06/1.29  thf('43', plain,
% 1.06/1.29      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 1.06/1.29         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.06/1.29      inference('demod', [status(thm)], ['12', '13'])).
% 1.06/1.29  thf('44', plain,
% 1.06/1.29      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A))
% 1.06/1.29         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 1.06/1.29             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.06/1.29      inference('sup+', [status(thm)], ['42', '43'])).
% 1.06/1.29  thf('45', plain,
% 1.06/1.29      (![X23 : $i, X24 : $i]:
% 1.06/1.29         ((r2_hidden @ X23 @ (k1_ordinal1 @ X24)) | ((X23) != (X24)))),
% 1.06/1.29      inference('cnf', [status(esa)], [t13_ordinal1])).
% 1.06/1.29  thf('46', plain, (![X24 : $i]: (r2_hidden @ X24 @ (k1_ordinal1 @ X24))),
% 1.06/1.29      inference('simplify', [status(thm)], ['45'])).
% 1.06/1.29  thf('47', plain,
% 1.06/1.29      (![X28 : $i, X29 : $i]:
% 1.06/1.29         (~ (r2_hidden @ X28 @ X29) | ~ (r1_tarski @ X29 @ X28))),
% 1.06/1.29      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.06/1.29  thf('48', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 1.06/1.29      inference('sup-', [status(thm)], ['46', '47'])).
% 1.06/1.29  thf('49', plain,
% 1.06/1.29      (((r2_hidden @ sk_A @ sk_B)) | 
% 1.06/1.29       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 1.06/1.29      inference('sup-', [status(thm)], ['44', '48'])).
% 1.06/1.29  thf('50', plain,
% 1.06/1.29      (((r2_hidden @ sk_A @ sk_B)) | 
% 1.06/1.29       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 1.06/1.29      inference('split', [status(esa)], ['0'])).
% 1.06/1.29  thf('51', plain, (((r2_hidden @ sk_A @ sk_B))),
% 1.06/1.29      inference('sat_resolution*', [status(thm)], ['5', '49', '50'])).
% 1.06/1.29  thf('52', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 1.06/1.29      inference('simpl_trail', [status(thm)], ['3', '51'])).
% 1.06/1.29  thf('53', plain,
% 1.06/1.29      (![X27 : $i]:
% 1.06/1.29         ((v3_ordinal1 @ (k1_ordinal1 @ X27)) | ~ (v3_ordinal1 @ X27))),
% 1.06/1.29      inference('cnf', [status(esa)], [t29_ordinal1])).
% 1.06/1.29  thf('54', plain,
% 1.06/1.29      (![X25 : $i, X26 : $i]:
% 1.06/1.29         (~ (v3_ordinal1 @ X25)
% 1.06/1.29          | (r1_ordinal1 @ X26 @ X25)
% 1.06/1.29          | (r2_hidden @ X25 @ X26)
% 1.06/1.29          | ~ (v3_ordinal1 @ X26))),
% 1.06/1.29      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.06/1.29  thf('55', plain,
% 1.06/1.29      (![X22 : $i, X23 : $i]:
% 1.06/1.29         (((X23) = (X22))
% 1.06/1.29          | (r2_hidden @ X23 @ X22)
% 1.06/1.29          | ~ (r2_hidden @ X23 @ (k1_ordinal1 @ X22)))),
% 1.06/1.29      inference('cnf', [status(esa)], [t13_ordinal1])).
% 1.06/1.29  thf('56', plain,
% 1.06/1.29      (![X0 : $i, X1 : $i]:
% 1.06/1.29         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 1.06/1.29          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 1.06/1.29          | ~ (v3_ordinal1 @ X1)
% 1.06/1.29          | (r2_hidden @ X1 @ X0)
% 1.06/1.29          | ((X1) = (X0)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['54', '55'])).
% 1.06/1.29  thf('57', plain,
% 1.06/1.29      (![X0 : $i, X1 : $i]:
% 1.06/1.29         (~ (v3_ordinal1 @ X0)
% 1.06/1.29          | ((X1) = (X0))
% 1.06/1.29          | (r2_hidden @ X1 @ X0)
% 1.06/1.29          | ~ (v3_ordinal1 @ X1)
% 1.06/1.29          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1))),
% 1.06/1.29      inference('sup-', [status(thm)], ['53', '56'])).
% 1.06/1.29  thf('58', plain,
% 1.06/1.29      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 1.06/1.29         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.06/1.29      inference('split', [status(esa)], ['4'])).
% 1.06/1.29  thf('59', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 1.06/1.29      inference('sat_resolution*', [status(thm)], ['5', '49'])).
% 1.06/1.29  thf('60', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 1.06/1.29      inference('simpl_trail', [status(thm)], ['58', '59'])).
% 1.06/1.29  thf('61', plain,
% 1.06/1.29      ((~ (v3_ordinal1 @ sk_B)
% 1.06/1.29        | (r2_hidden @ sk_B @ sk_A)
% 1.06/1.29        | ((sk_B) = (sk_A))
% 1.06/1.29        | ~ (v3_ordinal1 @ sk_A))),
% 1.06/1.29      inference('sup-', [status(thm)], ['57', '60'])).
% 1.06/1.29  thf('62', plain, ((v3_ordinal1 @ sk_B)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('63', plain, ((v3_ordinal1 @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('64', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 1.06/1.29      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.06/1.29  thf('65', plain,
% 1.06/1.29      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.06/1.29      inference('split', [status(esa)], ['0'])).
% 1.06/1.29  thf(antisymmetry_r2_hidden, axiom,
% 1.06/1.29    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 1.06/1.29  thf('66', plain,
% 1.06/1.29      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 1.06/1.29      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 1.06/1.29  thf('67', plain,
% 1.06/1.29      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['65', '66'])).
% 1.06/1.29  thf('68', plain, (((r2_hidden @ sk_A @ sk_B))),
% 1.06/1.29      inference('sat_resolution*', [status(thm)], ['5', '49', '50'])).
% 1.06/1.29  thf('69', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 1.06/1.29      inference('simpl_trail', [status(thm)], ['67', '68'])).
% 1.06/1.29  thf('70', plain, (((sk_B) = (sk_A))),
% 1.06/1.29      inference('clc', [status(thm)], ['64', '69'])).
% 1.06/1.29  thf('71', plain,
% 1.06/1.29      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 1.06/1.29      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.06/1.29  thf('72', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 1.06/1.29      inference('simplify', [status(thm)], ['71'])).
% 1.06/1.29  thf('73', plain, ($false),
% 1.06/1.29      inference('demod', [status(thm)], ['52', '70', '72'])).
% 1.06/1.29  
% 1.06/1.29  % SZS output end Refutation
% 1.06/1.29  
% 1.06/1.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
