%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xWbgRyt6HA

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:05 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 168 expanded)
%              Number of leaves         :   24 (  56 expanded)
%              Depth                    :   15
%              Number of atoms          :  736 (1335 expanded)
%              Number of equality atoms :   32 (  48 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X73: $i,X74: $i] :
      ( ~ ( v3_ordinal1 @ X73 )
      | ( r1_ordinal1 @ X74 @ X73 )
      | ( r2_hidden @ X73 @ X74 )
      | ~ ( v3_ordinal1 @ X74 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( r2_hidden @ X75 @ X76 )
      | ~ ( r1_tarski @ X76 @ X75 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['9'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('11',plain,(
    ! [X67: $i] :
      ( ( k1_ordinal1 @ X67 )
      = ( k2_xboole_0 @ X67 @ ( k1_tarski @ X67 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X42 @ X43 ) )
      = ( k2_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X67: $i] :
      ( ( k1_ordinal1 @ X67 )
      = ( k3_tarski @ ( k2_tarski @ X67 @ ( k1_tarski @ X67 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('15',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X42 @ X43 ) )
      = ( k2_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('17',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( X12 = X9 )
      | ( X11
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('21',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12 = X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ( sk_A = sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( r2_hidden @ X68 @ X69 )
      | ( r1_tarski @ X68 @ X69 )
      | ~ ( v1_ordinal1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('24',plain,
    ( ( ( sk_A = sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('26',plain,(
    ! [X66: $i] :
      ( ( v1_ordinal1 @ X66 )
      | ~ ( v3_ordinal1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('27',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('30',plain,
    ( ( ( sk_A = sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( sk_A = sk_B_1 )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','37'])).

thf('39',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['9'])).

thf('42',plain,(
    ! [X67: $i] :
      ( ( k1_ordinal1 @ X67 )
      = ( k3_tarski @ ( k2_tarski @ X67 @ ( k1_tarski @ X67 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('43',plain,(
    ! [X73: $i,X74: $i] :
      ( ~ ( v3_ordinal1 @ X73 )
      | ( r1_ordinal1 @ X74 @ X73 )
      | ( r2_hidden @ X73 @ X74 )
      | ~ ( v3_ordinal1 @ X74 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X42 @ X43 ) )
      = ( k2_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k3_tarski @ ( k2_tarski @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r1_ordinal1 @ sk_B_1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( r1_ordinal1 @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('55',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( v3_ordinal1 @ X71 )
      | ~ ( v3_ordinal1 @ X72 )
      | ( r1_tarski @ X71 @ X72 )
      | ~ ( r1_ordinal1 @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('56',plain,
    ( ( ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('61',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( v3_ordinal1 @ X71 )
      | ~ ( v3_ordinal1 @ X72 )
      | ( r1_tarski @ X71 @ X72 )
      | ~ ( r1_ordinal1 @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('62',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('67',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ( sk_B_1 = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_B_1 = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['59','67'])).

thf('69',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X67: $i] :
      ( ( k1_ordinal1 @ X67 )
      = ( k3_tarski @ ( k2_tarski @ X67 @ ( k1_tarski @ X67 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('72',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X10 != X9 )
      | ( r2_hidden @ X10 @ X11 )
      | ( X11
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('73',plain,(
    ! [X9: $i] :
      ( r2_hidden @ X9 @ ( k1_tarski @ X9 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X42 @ X43 ) )
      = ( k2_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','78'])).

thf('80',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['70','79'])).

thf('81',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','40','41','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xWbgRyt6HA
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:58:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.64/1.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.64/1.87  % Solved by: fo/fo7.sh
% 1.64/1.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.64/1.87  % done 2549 iterations in 1.438s
% 1.64/1.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.64/1.87  % SZS output start Refutation
% 1.64/1.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.64/1.87  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 1.64/1.87  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.64/1.87  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 1.64/1.87  thf(sk_A_type, type, sk_A: $i).
% 1.64/1.87  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 1.64/1.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.64/1.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.64/1.87  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.64/1.87  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 1.64/1.87  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.64/1.87  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 1.64/1.87  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.64/1.87  thf(t34_ordinal1, conjecture,
% 1.64/1.87    (![A:$i]:
% 1.64/1.87     ( ( v3_ordinal1 @ A ) =>
% 1.64/1.87       ( ![B:$i]:
% 1.64/1.87         ( ( v3_ordinal1 @ B ) =>
% 1.64/1.87           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 1.64/1.87             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 1.64/1.87  thf(zf_stmt_0, negated_conjecture,
% 1.64/1.87    (~( ![A:$i]:
% 1.64/1.87        ( ( v3_ordinal1 @ A ) =>
% 1.64/1.87          ( ![B:$i]:
% 1.64/1.87            ( ( v3_ordinal1 @ B ) =>
% 1.64/1.87              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 1.64/1.87                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 1.64/1.87    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 1.64/1.87  thf('0', plain,
% 1.64/1.87      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)
% 1.64/1.87        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('1', plain,
% 1.64/1.87      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 1.64/1.87       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 1.64/1.87      inference('split', [status(esa)], ['0'])).
% 1.64/1.87  thf(d10_xboole_0, axiom,
% 1.64/1.87    (![A:$i,B:$i]:
% 1.64/1.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.64/1.87  thf('2', plain,
% 1.64/1.87      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 1.64/1.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.64/1.87  thf('3', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 1.64/1.87      inference('simplify', [status(thm)], ['2'])).
% 1.64/1.87  thf(t26_ordinal1, axiom,
% 1.64/1.87    (![A:$i]:
% 1.64/1.87     ( ( v3_ordinal1 @ A ) =>
% 1.64/1.87       ( ![B:$i]:
% 1.64/1.87         ( ( v3_ordinal1 @ B ) =>
% 1.64/1.87           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 1.64/1.87  thf('4', plain,
% 1.64/1.87      (![X73 : $i, X74 : $i]:
% 1.64/1.87         (~ (v3_ordinal1 @ X73)
% 1.64/1.87          | (r1_ordinal1 @ X74 @ X73)
% 1.64/1.87          | (r2_hidden @ X73 @ X74)
% 1.64/1.87          | ~ (v3_ordinal1 @ X74))),
% 1.64/1.87      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.64/1.87  thf(t7_ordinal1, axiom,
% 1.64/1.87    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.64/1.87  thf('5', plain,
% 1.64/1.87      (![X75 : $i, X76 : $i]:
% 1.64/1.87         (~ (r2_hidden @ X75 @ X76) | ~ (r1_tarski @ X76 @ X75))),
% 1.64/1.87      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.64/1.87  thf('6', plain,
% 1.64/1.87      (![X0 : $i, X1 : $i]:
% 1.64/1.87         (~ (v3_ordinal1 @ X0)
% 1.64/1.87          | (r1_ordinal1 @ X0 @ X1)
% 1.64/1.87          | ~ (v3_ordinal1 @ X1)
% 1.64/1.87          | ~ (r1_tarski @ X0 @ X1))),
% 1.64/1.87      inference('sup-', [status(thm)], ['4', '5'])).
% 1.64/1.87  thf('7', plain,
% 1.64/1.87      (![X0 : $i]:
% 1.64/1.87         (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 1.64/1.87      inference('sup-', [status(thm)], ['3', '6'])).
% 1.64/1.87  thf('8', plain,
% 1.64/1.87      (![X0 : $i]: ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 1.64/1.87      inference('simplify', [status(thm)], ['7'])).
% 1.64/1.87  thf('9', plain,
% 1.64/1.87      (((r1_ordinal1 @ sk_A @ sk_B_1)
% 1.64/1.87        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('10', plain,
% 1.64/1.87      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 1.64/1.87         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 1.64/1.87      inference('split', [status(esa)], ['9'])).
% 1.64/1.87  thf(d1_ordinal1, axiom,
% 1.64/1.87    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 1.64/1.87  thf('11', plain,
% 1.64/1.87      (![X67 : $i]:
% 1.64/1.87         ((k1_ordinal1 @ X67) = (k2_xboole_0 @ X67 @ (k1_tarski @ X67)))),
% 1.64/1.87      inference('cnf', [status(esa)], [d1_ordinal1])).
% 1.64/1.87  thf(l51_zfmisc_1, axiom,
% 1.64/1.87    (![A:$i,B:$i]:
% 1.64/1.87     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.64/1.87  thf('12', plain,
% 1.64/1.87      (![X42 : $i, X43 : $i]:
% 1.64/1.87         ((k3_tarski @ (k2_tarski @ X42 @ X43)) = (k2_xboole_0 @ X42 @ X43))),
% 1.64/1.87      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.64/1.87  thf('13', plain,
% 1.64/1.87      (![X67 : $i]:
% 1.64/1.87         ((k1_ordinal1 @ X67)
% 1.64/1.87           = (k3_tarski @ (k2_tarski @ X67 @ (k1_tarski @ X67))))),
% 1.64/1.87      inference('demod', [status(thm)], ['11', '12'])).
% 1.64/1.87  thf(d3_xboole_0, axiom,
% 1.64/1.87    (![A:$i,B:$i,C:$i]:
% 1.64/1.87     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.64/1.87       ( ![D:$i]:
% 1.64/1.87         ( ( r2_hidden @ D @ C ) <=>
% 1.64/1.87           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.64/1.87  thf('14', plain,
% 1.64/1.87      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.64/1.87         (~ (r2_hidden @ X4 @ X2)
% 1.64/1.87          | (r2_hidden @ X4 @ X3)
% 1.64/1.87          | (r2_hidden @ X4 @ X1)
% 1.64/1.87          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.64/1.87      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.64/1.87  thf('15', plain,
% 1.64/1.87      (![X1 : $i, X3 : $i, X4 : $i]:
% 1.64/1.87         ((r2_hidden @ X4 @ X1)
% 1.64/1.87          | (r2_hidden @ X4 @ X3)
% 1.64/1.87          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 1.64/1.87      inference('simplify', [status(thm)], ['14'])).
% 1.64/1.87  thf('16', plain,
% 1.64/1.87      (![X42 : $i, X43 : $i]:
% 1.64/1.87         ((k3_tarski @ (k2_tarski @ X42 @ X43)) = (k2_xboole_0 @ X42 @ X43))),
% 1.64/1.87      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.64/1.87  thf('17', plain,
% 1.64/1.87      (![X1 : $i, X3 : $i, X4 : $i]:
% 1.64/1.87         ((r2_hidden @ X4 @ X1)
% 1.64/1.87          | (r2_hidden @ X4 @ X3)
% 1.64/1.87          | ~ (r2_hidden @ X4 @ (k3_tarski @ (k2_tarski @ X3 @ X1))))),
% 1.64/1.87      inference('demod', [status(thm)], ['15', '16'])).
% 1.64/1.87  thf('18', plain,
% 1.64/1.87      (![X0 : $i, X1 : $i]:
% 1.64/1.87         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 1.64/1.87          | (r2_hidden @ X1 @ X0)
% 1.64/1.87          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.64/1.87      inference('sup-', [status(thm)], ['13', '17'])).
% 1.64/1.87  thf('19', plain,
% 1.64/1.87      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))
% 1.64/1.87         | (r2_hidden @ sk_A @ sk_B_1)))
% 1.64/1.87         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['10', '18'])).
% 1.64/1.87  thf(d1_tarski, axiom,
% 1.64/1.87    (![A:$i,B:$i]:
% 1.64/1.87     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.64/1.87       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.64/1.87  thf('20', plain,
% 1.64/1.87      (![X9 : $i, X11 : $i, X12 : $i]:
% 1.64/1.87         (~ (r2_hidden @ X12 @ X11)
% 1.64/1.87          | ((X12) = (X9))
% 1.64/1.87          | ((X11) != (k1_tarski @ X9)))),
% 1.64/1.87      inference('cnf', [status(esa)], [d1_tarski])).
% 1.64/1.87  thf('21', plain,
% 1.64/1.87      (![X9 : $i, X12 : $i]:
% 1.64/1.87         (((X12) = (X9)) | ~ (r2_hidden @ X12 @ (k1_tarski @ X9)))),
% 1.64/1.87      inference('simplify', [status(thm)], ['20'])).
% 1.64/1.87  thf('22', plain,
% 1.64/1.87      ((((r2_hidden @ sk_A @ sk_B_1) | ((sk_A) = (sk_B_1))))
% 1.64/1.87         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['19', '21'])).
% 1.64/1.87  thf(d2_ordinal1, axiom,
% 1.64/1.87    (![A:$i]:
% 1.64/1.87     ( ( v1_ordinal1 @ A ) <=>
% 1.64/1.87       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 1.64/1.87  thf('23', plain,
% 1.64/1.87      (![X68 : $i, X69 : $i]:
% 1.64/1.87         (~ (r2_hidden @ X68 @ X69)
% 1.64/1.87          | (r1_tarski @ X68 @ X69)
% 1.64/1.87          | ~ (v1_ordinal1 @ X69))),
% 1.64/1.87      inference('cnf', [status(esa)], [d2_ordinal1])).
% 1.64/1.87  thf('24', plain,
% 1.64/1.87      (((((sk_A) = (sk_B_1))
% 1.64/1.87         | ~ (v1_ordinal1 @ sk_B_1)
% 1.64/1.87         | (r1_tarski @ sk_A @ sk_B_1)))
% 1.64/1.87         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['22', '23'])).
% 1.64/1.87  thf('25', plain, ((v3_ordinal1 @ sk_B_1)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf(cc1_ordinal1, axiom,
% 1.64/1.87    (![A:$i]:
% 1.64/1.87     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 1.64/1.87  thf('26', plain,
% 1.64/1.87      (![X66 : $i]: ((v1_ordinal1 @ X66) | ~ (v3_ordinal1 @ X66))),
% 1.64/1.87      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 1.64/1.87  thf('27', plain, ((v1_ordinal1 @ sk_B_1)),
% 1.64/1.87      inference('sup-', [status(thm)], ['25', '26'])).
% 1.64/1.87  thf('28', plain,
% 1.64/1.87      (((((sk_A) = (sk_B_1)) | (r1_tarski @ sk_A @ sk_B_1)))
% 1.64/1.87         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 1.64/1.87      inference('demod', [status(thm)], ['24', '27'])).
% 1.64/1.87  thf('29', plain,
% 1.64/1.87      (![X0 : $i, X1 : $i]:
% 1.64/1.87         (~ (v3_ordinal1 @ X0)
% 1.64/1.87          | (r1_ordinal1 @ X0 @ X1)
% 1.64/1.87          | ~ (v3_ordinal1 @ X1)
% 1.64/1.87          | ~ (r1_tarski @ X0 @ X1))),
% 1.64/1.87      inference('sup-', [status(thm)], ['4', '5'])).
% 1.64/1.87  thf('30', plain,
% 1.64/1.87      (((((sk_A) = (sk_B_1))
% 1.64/1.87         | ~ (v3_ordinal1 @ sk_B_1)
% 1.64/1.87         | (r1_ordinal1 @ sk_A @ sk_B_1)
% 1.64/1.87         | ~ (v3_ordinal1 @ sk_A)))
% 1.64/1.87         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['28', '29'])).
% 1.64/1.87  thf('31', plain, ((v3_ordinal1 @ sk_B_1)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('32', plain, ((v3_ordinal1 @ sk_A)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('33', plain,
% 1.64/1.87      (((((sk_A) = (sk_B_1)) | (r1_ordinal1 @ sk_A @ sk_B_1)))
% 1.64/1.87         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 1.64/1.87      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.64/1.87  thf('34', plain,
% 1.64/1.87      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 1.64/1.87      inference('split', [status(esa)], ['0'])).
% 1.64/1.87  thf('35', plain,
% 1.64/1.87      ((((sk_A) = (sk_B_1)))
% 1.64/1.87         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 1.64/1.87             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['33', '34'])).
% 1.64/1.87  thf('36', plain,
% 1.64/1.87      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 1.64/1.87      inference('split', [status(esa)], ['0'])).
% 1.64/1.87  thf('37', plain,
% 1.64/1.87      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 1.64/1.87         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 1.64/1.87             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['35', '36'])).
% 1.64/1.87  thf('38', plain,
% 1.64/1.87      ((~ (v3_ordinal1 @ sk_A))
% 1.64/1.87         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 1.64/1.87             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['8', '37'])).
% 1.64/1.87  thf('39', plain, ((v3_ordinal1 @ sk_A)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('40', plain,
% 1.64/1.87      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 1.64/1.87       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 1.64/1.87      inference('demod', [status(thm)], ['38', '39'])).
% 1.64/1.87  thf('41', plain,
% 1.64/1.87      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 1.64/1.87       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 1.64/1.87      inference('split', [status(esa)], ['9'])).
% 1.64/1.87  thf('42', plain,
% 1.64/1.87      (![X67 : $i]:
% 1.64/1.87         ((k1_ordinal1 @ X67)
% 1.64/1.87           = (k3_tarski @ (k2_tarski @ X67 @ (k1_tarski @ X67))))),
% 1.64/1.87      inference('demod', [status(thm)], ['11', '12'])).
% 1.64/1.87  thf('43', plain,
% 1.64/1.87      (![X73 : $i, X74 : $i]:
% 1.64/1.87         (~ (v3_ordinal1 @ X73)
% 1.64/1.87          | (r1_ordinal1 @ X74 @ X73)
% 1.64/1.87          | (r2_hidden @ X73 @ X74)
% 1.64/1.87          | ~ (v3_ordinal1 @ X74))),
% 1.64/1.87      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.64/1.87  thf('44', plain,
% 1.64/1.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.64/1.87         (~ (r2_hidden @ X0 @ X3)
% 1.64/1.87          | (r2_hidden @ X0 @ X2)
% 1.64/1.87          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.64/1.87      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.64/1.87  thf('45', plain,
% 1.64/1.87      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.64/1.87         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 1.64/1.87      inference('simplify', [status(thm)], ['44'])).
% 1.64/1.87  thf('46', plain,
% 1.64/1.87      (![X42 : $i, X43 : $i]:
% 1.64/1.87         ((k3_tarski @ (k2_tarski @ X42 @ X43)) = (k2_xboole_0 @ X42 @ X43))),
% 1.64/1.87      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.64/1.87  thf('47', plain,
% 1.64/1.87      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.64/1.87         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 1.64/1.87          | ~ (r2_hidden @ X0 @ X3))),
% 1.64/1.87      inference('demod', [status(thm)], ['45', '46'])).
% 1.64/1.87  thf('48', plain,
% 1.64/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.87         (~ (v3_ordinal1 @ X0)
% 1.64/1.87          | (r1_ordinal1 @ X0 @ X1)
% 1.64/1.87          | ~ (v3_ordinal1 @ X1)
% 1.64/1.87          | (r2_hidden @ X1 @ (k3_tarski @ (k2_tarski @ X0 @ X2))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['43', '47'])).
% 1.64/1.87  thf('49', plain,
% 1.64/1.87      (![X0 : $i, X1 : $i]:
% 1.64/1.87         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 1.64/1.87          | ~ (v3_ordinal1 @ X1)
% 1.64/1.87          | (r1_ordinal1 @ X0 @ X1)
% 1.64/1.87          | ~ (v3_ordinal1 @ X0))),
% 1.64/1.87      inference('sup+', [status(thm)], ['42', '48'])).
% 1.64/1.87  thf('50', plain,
% 1.64/1.87      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 1.64/1.87         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 1.64/1.87      inference('split', [status(esa)], ['0'])).
% 1.64/1.87  thf('51', plain,
% 1.64/1.87      (((~ (v3_ordinal1 @ sk_B_1)
% 1.64/1.87         | (r1_ordinal1 @ sk_B_1 @ sk_A)
% 1.64/1.87         | ~ (v3_ordinal1 @ sk_A)))
% 1.64/1.87         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['49', '50'])).
% 1.64/1.87  thf('52', plain, ((v3_ordinal1 @ sk_B_1)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('53', plain, ((v3_ordinal1 @ sk_A)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('54', plain,
% 1.64/1.87      (((r1_ordinal1 @ sk_B_1 @ sk_A))
% 1.64/1.87         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 1.64/1.87      inference('demod', [status(thm)], ['51', '52', '53'])).
% 1.64/1.87  thf(redefinition_r1_ordinal1, axiom,
% 1.64/1.87    (![A:$i,B:$i]:
% 1.64/1.87     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 1.64/1.87       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 1.64/1.87  thf('55', plain,
% 1.64/1.87      (![X71 : $i, X72 : $i]:
% 1.64/1.87         (~ (v3_ordinal1 @ X71)
% 1.64/1.87          | ~ (v3_ordinal1 @ X72)
% 1.64/1.87          | (r1_tarski @ X71 @ X72)
% 1.64/1.87          | ~ (r1_ordinal1 @ X71 @ X72))),
% 1.64/1.87      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.64/1.87  thf('56', plain,
% 1.64/1.87      ((((r1_tarski @ sk_B_1 @ sk_A)
% 1.64/1.87         | ~ (v3_ordinal1 @ sk_A)
% 1.64/1.87         | ~ (v3_ordinal1 @ sk_B_1)))
% 1.64/1.87         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['54', '55'])).
% 1.64/1.87  thf('57', plain, ((v3_ordinal1 @ sk_A)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('58', plain, ((v3_ordinal1 @ sk_B_1)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('59', plain,
% 1.64/1.87      (((r1_tarski @ sk_B_1 @ sk_A))
% 1.64/1.87         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 1.64/1.87      inference('demod', [status(thm)], ['56', '57', '58'])).
% 1.64/1.87  thf('60', plain,
% 1.64/1.87      (((r1_ordinal1 @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 1.64/1.87      inference('split', [status(esa)], ['9'])).
% 1.64/1.87  thf('61', plain,
% 1.64/1.87      (![X71 : $i, X72 : $i]:
% 1.64/1.87         (~ (v3_ordinal1 @ X71)
% 1.64/1.87          | ~ (v3_ordinal1 @ X72)
% 1.64/1.87          | (r1_tarski @ X71 @ X72)
% 1.64/1.87          | ~ (r1_ordinal1 @ X71 @ X72))),
% 1.64/1.87      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.64/1.87  thf('62', plain,
% 1.64/1.87      ((((r1_tarski @ sk_A @ sk_B_1)
% 1.64/1.87         | ~ (v3_ordinal1 @ sk_B_1)
% 1.64/1.87         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 1.64/1.87      inference('sup-', [status(thm)], ['60', '61'])).
% 1.64/1.87  thf('63', plain, ((v3_ordinal1 @ sk_B_1)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('64', plain, ((v3_ordinal1 @ sk_A)),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('65', plain,
% 1.64/1.87      (((r1_tarski @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 1.64/1.87      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.64/1.87  thf('66', plain,
% 1.64/1.87      (![X6 : $i, X8 : $i]:
% 1.64/1.87         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.64/1.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.64/1.87  thf('67', plain,
% 1.64/1.87      (((~ (r1_tarski @ sk_B_1 @ sk_A) | ((sk_B_1) = (sk_A))))
% 1.64/1.87         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 1.64/1.87      inference('sup-', [status(thm)], ['65', '66'])).
% 1.64/1.87  thf('68', plain,
% 1.64/1.87      ((((sk_B_1) = (sk_A)))
% 1.64/1.87         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 1.64/1.87             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 1.64/1.87      inference('sup-', [status(thm)], ['59', '67'])).
% 1.64/1.87  thf('69', plain,
% 1.64/1.87      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 1.64/1.87         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 1.64/1.87      inference('split', [status(esa)], ['0'])).
% 1.64/1.87  thf('70', plain,
% 1.64/1.87      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 1.64/1.87         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 1.64/1.87             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 1.64/1.87      inference('sup-', [status(thm)], ['68', '69'])).
% 1.64/1.87  thf('71', plain,
% 1.64/1.87      (![X67 : $i]:
% 1.64/1.87         ((k1_ordinal1 @ X67)
% 1.64/1.87           = (k3_tarski @ (k2_tarski @ X67 @ (k1_tarski @ X67))))),
% 1.64/1.87      inference('demod', [status(thm)], ['11', '12'])).
% 1.64/1.87  thf('72', plain,
% 1.64/1.87      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.64/1.87         (((X10) != (X9))
% 1.64/1.87          | (r2_hidden @ X10 @ X11)
% 1.64/1.87          | ((X11) != (k1_tarski @ X9)))),
% 1.64/1.87      inference('cnf', [status(esa)], [d1_tarski])).
% 1.64/1.87  thf('73', plain, (![X9 : $i]: (r2_hidden @ X9 @ (k1_tarski @ X9))),
% 1.64/1.87      inference('simplify', [status(thm)], ['72'])).
% 1.64/1.87  thf('74', plain,
% 1.64/1.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.64/1.87         (~ (r2_hidden @ X0 @ X1)
% 1.64/1.87          | (r2_hidden @ X0 @ X2)
% 1.64/1.87          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.64/1.87      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.64/1.87  thf('75', plain,
% 1.64/1.87      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.64/1.87         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 1.64/1.87      inference('simplify', [status(thm)], ['74'])).
% 1.64/1.87  thf('76', plain,
% 1.64/1.87      (![X42 : $i, X43 : $i]:
% 1.64/1.87         ((k3_tarski @ (k2_tarski @ X42 @ X43)) = (k2_xboole_0 @ X42 @ X43))),
% 1.64/1.87      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.64/1.87  thf('77', plain,
% 1.64/1.87      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.64/1.87         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 1.64/1.87          | ~ (r2_hidden @ X0 @ X1))),
% 1.64/1.87      inference('demod', [status(thm)], ['75', '76'])).
% 1.64/1.87  thf('78', plain,
% 1.64/1.87      (![X0 : $i, X1 : $i]:
% 1.64/1.87         (r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ (k1_tarski @ X0))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['73', '77'])).
% 1.64/1.87  thf('79', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 1.64/1.87      inference('sup+', [status(thm)], ['71', '78'])).
% 1.64/1.87  thf('80', plain,
% 1.64/1.87      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 1.64/1.87       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 1.64/1.87      inference('demod', [status(thm)], ['70', '79'])).
% 1.64/1.87  thf('81', plain, ($false),
% 1.64/1.87      inference('sat_resolution*', [status(thm)], ['1', '40', '41', '80'])).
% 1.64/1.87  
% 1.64/1.87  % SZS output end Refutation
% 1.64/1.87  
% 1.64/1.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
