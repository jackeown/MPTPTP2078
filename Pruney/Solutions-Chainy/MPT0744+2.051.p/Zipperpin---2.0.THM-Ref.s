%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lYMf7PBjUi

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:06 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 310 expanded)
%              Number of leaves         :   20 (  92 expanded)
%              Depth                    :   20
%              Number of atoms          :  668 (2512 expanded)
%              Number of equality atoms :   17 (  60 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

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
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('4',plain,(
    ! [X66: $i] :
      ( ( k1_ordinal1 @ X66 )
      = ( k2_xboole_0 @ X66 @ ( k1_tarski @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( v3_ordinal1 @ X69 )
      | ( r1_ordinal1 @ X70 @ X69 )
      | ( r2_hidden @ X69 @ X70 )
      | ~ ( v3_ordinal1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( v3_ordinal1 @ X67 )
      | ~ ( v3_ordinal1 @ X68 )
      | ( r1_tarski @ X67 @ X68 )
      | ~ ( r1_ordinal1 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('17',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( v3_ordinal1 @ X67 )
      | ~ ( v3_ordinal1 @ X68 )
      | ( r1_tarski @ X67 @ X68 )
      | ~ ( r1_ordinal1 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('24',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X66: $i] :
      ( ( k1_ordinal1 @ X66 )
      = ( k2_xboole_0 @ X66 @ ( k1_tarski @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['34'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('36',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r2_hidden @ X37 @ X38 )
      | ~ ( r1_tarski @ ( k1_tarski @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['32','41'])).

thf('43',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','42'])).

thf('44',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','43'])).

thf('45',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v3_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X65 )
      | ( r1_ordinal1 @ X64 @ X65 )
      | ( r1_ordinal1 @ X65 @ X64 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( v3_ordinal1 @ X67 )
      | ~ ( v3_ordinal1 @ X68 )
      | ( r1_tarski @ X67 @ X68 )
      | ~ ( r1_ordinal1 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( v3_ordinal1 @ X69 )
      | ( r1_ordinal1 @ X70 @ X69 )
      | ( r2_hidden @ X69 @ X70 )
      | ~ ( v3_ordinal1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('54',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X37 ) @ X39 )
      | ~ ( r2_hidden @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['21'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('58',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('59',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,
    ( ( ( r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_B ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','60'])).

thf('62',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('63',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('64',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('65',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf('67',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','42','66'])).

thf('68',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['65','67'])).

thf('69',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['55','68'])).

thf('70',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','43'])).

thf('74',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('76',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['52','76'])).

thf('78',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['44','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lYMf7PBjUi
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.20/1.40  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.20/1.40  % Solved by: fo/fo7.sh
% 1.20/1.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.40  % done 2019 iterations in 0.947s
% 1.20/1.40  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.20/1.40  % SZS output start Refutation
% 1.20/1.40  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.20/1.40  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 1.20/1.40  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.20/1.40  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.20/1.40  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.20/1.40  thf(sk_B_type, type, sk_B: $i).
% 1.20/1.40  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 1.20/1.40  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.20/1.40  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 1.20/1.40  thf(t34_ordinal1, conjecture,
% 1.20/1.40    (![A:$i]:
% 1.20/1.40     ( ( v3_ordinal1 @ A ) =>
% 1.20/1.40       ( ![B:$i]:
% 1.20/1.40         ( ( v3_ordinal1 @ B ) =>
% 1.20/1.40           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 1.20/1.40             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 1.20/1.40  thf(zf_stmt_0, negated_conjecture,
% 1.20/1.40    (~( ![A:$i]:
% 1.20/1.40        ( ( v3_ordinal1 @ A ) =>
% 1.20/1.40          ( ![B:$i]:
% 1.20/1.40            ( ( v3_ordinal1 @ B ) =>
% 1.20/1.40              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 1.20/1.40                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 1.20/1.40    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 1.20/1.40  thf('0', plain,
% 1.20/1.40      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 1.20/1.40        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('1', plain,
% 1.20/1.40      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.20/1.40      inference('split', [status(esa)], ['0'])).
% 1.20/1.40  thf('2', plain,
% 1.20/1.40      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 1.20/1.40       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.20/1.40      inference('split', [status(esa)], ['0'])).
% 1.20/1.40  thf(t69_enumset1, axiom,
% 1.20/1.40    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.20/1.40  thf('3', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 1.20/1.40      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.20/1.40  thf(d1_ordinal1, axiom,
% 1.20/1.40    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 1.20/1.40  thf('4', plain,
% 1.20/1.40      (![X66 : $i]:
% 1.20/1.40         ((k1_ordinal1 @ X66) = (k2_xboole_0 @ X66 @ (k1_tarski @ X66)))),
% 1.20/1.40      inference('cnf', [status(esa)], [d1_ordinal1])).
% 1.20/1.40  thf('5', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 1.20/1.40      inference('sup+', [status(thm)], ['3', '4'])).
% 1.20/1.40  thf(t26_ordinal1, axiom,
% 1.20/1.40    (![A:$i]:
% 1.20/1.40     ( ( v3_ordinal1 @ A ) =>
% 1.20/1.40       ( ![B:$i]:
% 1.20/1.40         ( ( v3_ordinal1 @ B ) =>
% 1.20/1.40           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 1.20/1.40  thf('6', plain,
% 1.20/1.40      (![X69 : $i, X70 : $i]:
% 1.20/1.40         (~ (v3_ordinal1 @ X69)
% 1.20/1.40          | (r1_ordinal1 @ X70 @ X69)
% 1.20/1.40          | (r2_hidden @ X69 @ X70)
% 1.20/1.40          | ~ (v3_ordinal1 @ X70))),
% 1.20/1.40      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.20/1.40  thf(d3_xboole_0, axiom,
% 1.20/1.40    (![A:$i,B:$i,C:$i]:
% 1.20/1.40     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.20/1.40       ( ![D:$i]:
% 1.20/1.40         ( ( r2_hidden @ D @ C ) <=>
% 1.20/1.40           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.20/1.40  thf('7', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.20/1.40         (~ (r2_hidden @ X0 @ X3)
% 1.20/1.40          | (r2_hidden @ X0 @ X2)
% 1.20/1.40          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.20/1.40      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.20/1.40  thf('8', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.20/1.40         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 1.20/1.40      inference('simplify', [status(thm)], ['7'])).
% 1.20/1.40  thf('9', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.40         (~ (v3_ordinal1 @ X0)
% 1.20/1.40          | (r1_ordinal1 @ X0 @ X1)
% 1.20/1.40          | ~ (v3_ordinal1 @ X1)
% 1.20/1.40          | (r2_hidden @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['6', '8'])).
% 1.20/1.40  thf('10', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i]:
% 1.20/1.40         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 1.20/1.40          | ~ (v3_ordinal1 @ X1)
% 1.20/1.40          | (r1_ordinal1 @ X0 @ X1)
% 1.20/1.40          | ~ (v3_ordinal1 @ X0))),
% 1.20/1.40      inference('sup+', [status(thm)], ['5', '9'])).
% 1.20/1.40  thf('11', plain,
% 1.20/1.40      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 1.20/1.40         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.20/1.40      inference('split', [status(esa)], ['0'])).
% 1.20/1.40  thf('12', plain,
% 1.20/1.40      (((~ (v3_ordinal1 @ sk_B)
% 1.20/1.40         | (r1_ordinal1 @ sk_B @ sk_A)
% 1.20/1.40         | ~ (v3_ordinal1 @ sk_A)))
% 1.20/1.40         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['10', '11'])).
% 1.20/1.40  thf('13', plain, ((v3_ordinal1 @ sk_B)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('14', plain, ((v3_ordinal1 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('15', plain,
% 1.20/1.40      (((r1_ordinal1 @ sk_B @ sk_A))
% 1.20/1.40         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.20/1.40      inference('demod', [status(thm)], ['12', '13', '14'])).
% 1.20/1.40  thf(redefinition_r1_ordinal1, axiom,
% 1.20/1.40    (![A:$i,B:$i]:
% 1.20/1.40     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 1.20/1.40       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 1.20/1.40  thf('16', plain,
% 1.20/1.40      (![X67 : $i, X68 : $i]:
% 1.20/1.40         (~ (v3_ordinal1 @ X67)
% 1.20/1.40          | ~ (v3_ordinal1 @ X68)
% 1.20/1.40          | (r1_tarski @ X67 @ X68)
% 1.20/1.40          | ~ (r1_ordinal1 @ X67 @ X68))),
% 1.20/1.40      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.20/1.40  thf('17', plain,
% 1.20/1.40      ((((r1_tarski @ sk_B @ sk_A)
% 1.20/1.40         | ~ (v3_ordinal1 @ sk_A)
% 1.20/1.40         | ~ (v3_ordinal1 @ sk_B)))
% 1.20/1.40         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['15', '16'])).
% 1.20/1.40  thf('18', plain, ((v3_ordinal1 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('19', plain, ((v3_ordinal1 @ sk_B)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('20', plain,
% 1.20/1.40      (((r1_tarski @ sk_B @ sk_A))
% 1.20/1.40         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.20/1.40      inference('demod', [status(thm)], ['17', '18', '19'])).
% 1.20/1.40  thf('21', plain,
% 1.20/1.40      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('22', plain,
% 1.20/1.40      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.20/1.40      inference('split', [status(esa)], ['21'])).
% 1.20/1.40  thf('23', plain,
% 1.20/1.40      (![X67 : $i, X68 : $i]:
% 1.20/1.40         (~ (v3_ordinal1 @ X67)
% 1.20/1.40          | ~ (v3_ordinal1 @ X68)
% 1.20/1.40          | (r1_tarski @ X67 @ X68)
% 1.20/1.40          | ~ (r1_ordinal1 @ X67 @ X68))),
% 1.20/1.40      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.20/1.40  thf('24', plain,
% 1.20/1.40      ((((r1_tarski @ sk_A @ sk_B)
% 1.20/1.40         | ~ (v3_ordinal1 @ sk_B)
% 1.20/1.40         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['22', '23'])).
% 1.20/1.40  thf('25', plain, ((v3_ordinal1 @ sk_B)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('26', plain, ((v3_ordinal1 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('27', plain,
% 1.20/1.40      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.20/1.40      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.20/1.40  thf(d10_xboole_0, axiom,
% 1.20/1.40    (![A:$i,B:$i]:
% 1.20/1.40     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.20/1.40  thf('28', plain,
% 1.20/1.40      (![X6 : $i, X8 : $i]:
% 1.20/1.40         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.20/1.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.20/1.40  thf('29', plain,
% 1.20/1.40      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A))))
% 1.20/1.40         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['27', '28'])).
% 1.20/1.40  thf('30', plain,
% 1.20/1.40      ((((sk_B) = (sk_A)))
% 1.20/1.40         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 1.20/1.40             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['20', '29'])).
% 1.20/1.40  thf('31', plain,
% 1.20/1.40      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 1.20/1.40         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.20/1.40      inference('split', [status(esa)], ['0'])).
% 1.20/1.40  thf('32', plain,
% 1.20/1.40      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 1.20/1.40         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 1.20/1.40             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['30', '31'])).
% 1.20/1.40  thf('33', plain,
% 1.20/1.40      (![X66 : $i]:
% 1.20/1.40         ((k1_ordinal1 @ X66) = (k2_xboole_0 @ X66 @ (k1_tarski @ X66)))),
% 1.20/1.40      inference('cnf', [status(esa)], [d1_ordinal1])).
% 1.20/1.40  thf('34', plain,
% 1.20/1.40      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 1.20/1.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.20/1.40  thf('35', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 1.20/1.40      inference('simplify', [status(thm)], ['34'])).
% 1.20/1.40  thf(l1_zfmisc_1, axiom,
% 1.20/1.40    (![A:$i,B:$i]:
% 1.20/1.40     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.20/1.40  thf('36', plain,
% 1.20/1.40      (![X37 : $i, X38 : $i]:
% 1.20/1.40         ((r2_hidden @ X37 @ X38) | ~ (r1_tarski @ (k1_tarski @ X37) @ X38))),
% 1.20/1.40      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.20/1.40  thf('37', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.20/1.40      inference('sup-', [status(thm)], ['35', '36'])).
% 1.20/1.40  thf('38', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.20/1.40         (~ (r2_hidden @ X0 @ X1)
% 1.20/1.40          | (r2_hidden @ X0 @ X2)
% 1.20/1.40          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.20/1.40      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.20/1.40  thf('39', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.20/1.40         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 1.20/1.40      inference('simplify', [status(thm)], ['38'])).
% 1.20/1.40  thf('40', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i]:
% 1.20/1.40         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['37', '39'])).
% 1.20/1.40  thf('41', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 1.20/1.40      inference('sup+', [status(thm)], ['33', '40'])).
% 1.20/1.40  thf('42', plain,
% 1.20/1.40      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | 
% 1.20/1.40       ~ ((r1_ordinal1 @ sk_A @ sk_B))),
% 1.20/1.40      inference('demod', [status(thm)], ['32', '41'])).
% 1.20/1.40  thf('43', plain, (~ ((r1_ordinal1 @ sk_A @ sk_B))),
% 1.20/1.40      inference('sat_resolution*', [status(thm)], ['2', '42'])).
% 1.20/1.40  thf('44', plain, (~ (r1_ordinal1 @ sk_A @ sk_B)),
% 1.20/1.40      inference('simpl_trail', [status(thm)], ['1', '43'])).
% 1.20/1.40  thf('45', plain, ((v3_ordinal1 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf(connectedness_r1_ordinal1, axiom,
% 1.20/1.40    (![A:$i,B:$i]:
% 1.20/1.40     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 1.20/1.40       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 1.20/1.40  thf('46', plain,
% 1.20/1.40      (![X64 : $i, X65 : $i]:
% 1.20/1.40         (~ (v3_ordinal1 @ X64)
% 1.20/1.40          | ~ (v3_ordinal1 @ X65)
% 1.20/1.40          | (r1_ordinal1 @ X64 @ X65)
% 1.20/1.40          | (r1_ordinal1 @ X65 @ X64))),
% 1.20/1.40      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 1.20/1.40  thf('47', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((r1_ordinal1 @ X0 @ sk_A)
% 1.20/1.40          | (r1_ordinal1 @ sk_A @ X0)
% 1.20/1.40          | ~ (v3_ordinal1 @ X0))),
% 1.20/1.40      inference('sup-', [status(thm)], ['45', '46'])).
% 1.20/1.40  thf('48', plain,
% 1.20/1.40      (![X67 : $i, X68 : $i]:
% 1.20/1.40         (~ (v3_ordinal1 @ X67)
% 1.20/1.40          | ~ (v3_ordinal1 @ X68)
% 1.20/1.40          | (r1_tarski @ X67 @ X68)
% 1.20/1.40          | ~ (r1_ordinal1 @ X67 @ X68))),
% 1.20/1.40      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.20/1.40  thf('49', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v3_ordinal1 @ X0)
% 1.20/1.40          | (r1_ordinal1 @ sk_A @ X0)
% 1.20/1.40          | (r1_tarski @ X0 @ sk_A)
% 1.20/1.40          | ~ (v3_ordinal1 @ sk_A)
% 1.20/1.40          | ~ (v3_ordinal1 @ X0))),
% 1.20/1.40      inference('sup-', [status(thm)], ['47', '48'])).
% 1.20/1.40  thf('50', plain, ((v3_ordinal1 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('51', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v3_ordinal1 @ X0)
% 1.20/1.40          | (r1_ordinal1 @ sk_A @ X0)
% 1.20/1.40          | (r1_tarski @ X0 @ sk_A)
% 1.20/1.40          | ~ (v3_ordinal1 @ X0))),
% 1.20/1.40      inference('demod', [status(thm)], ['49', '50'])).
% 1.20/1.40  thf('52', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((r1_tarski @ X0 @ sk_A)
% 1.20/1.40          | (r1_ordinal1 @ sk_A @ X0)
% 1.20/1.40          | ~ (v3_ordinal1 @ X0))),
% 1.20/1.40      inference('simplify', [status(thm)], ['51'])).
% 1.20/1.40  thf('53', plain,
% 1.20/1.40      (![X69 : $i, X70 : $i]:
% 1.20/1.40         (~ (v3_ordinal1 @ X69)
% 1.20/1.40          | (r1_ordinal1 @ X70 @ X69)
% 1.20/1.40          | (r2_hidden @ X69 @ X70)
% 1.20/1.40          | ~ (v3_ordinal1 @ X70))),
% 1.20/1.40      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.20/1.40  thf('54', plain,
% 1.20/1.40      (![X37 : $i, X39 : $i]:
% 1.20/1.40         ((r1_tarski @ (k1_tarski @ X37) @ X39) | ~ (r2_hidden @ X37 @ X39))),
% 1.20/1.40      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.20/1.40  thf('55', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i]:
% 1.20/1.40         (~ (v3_ordinal1 @ X0)
% 1.20/1.40          | (r1_ordinal1 @ X0 @ X1)
% 1.20/1.40          | ~ (v3_ordinal1 @ X1)
% 1.20/1.40          | (r1_tarski @ (k1_tarski @ X1) @ X0))),
% 1.20/1.40      inference('sup-', [status(thm)], ['53', '54'])).
% 1.20/1.40  thf('56', plain,
% 1.20/1.40      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 1.20/1.40         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.20/1.40      inference('split', [status(esa)], ['21'])).
% 1.20/1.40  thf('57', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 1.20/1.40      inference('sup+', [status(thm)], ['3', '4'])).
% 1.20/1.40  thf('58', plain,
% 1.20/1.40      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.20/1.40         (~ (r2_hidden @ X4 @ X2)
% 1.20/1.40          | (r2_hidden @ X4 @ X3)
% 1.20/1.40          | (r2_hidden @ X4 @ X1)
% 1.20/1.40          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.20/1.40      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.20/1.40  thf('59', plain,
% 1.20/1.40      (![X1 : $i, X3 : $i, X4 : $i]:
% 1.20/1.40         ((r2_hidden @ X4 @ X1)
% 1.20/1.40          | (r2_hidden @ X4 @ X3)
% 1.20/1.40          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 1.20/1.40      inference('simplify', [status(thm)], ['58'])).
% 1.20/1.40  thf('60', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i]:
% 1.20/1.40         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 1.20/1.40          | (r2_hidden @ X1 @ X0)
% 1.20/1.40          | (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['57', '59'])).
% 1.20/1.40  thf('61', plain,
% 1.20/1.40      ((((r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_B))
% 1.20/1.40         | (r2_hidden @ sk_A @ sk_B)))
% 1.20/1.40         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['56', '60'])).
% 1.20/1.40  thf('62', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 1.20/1.40      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.20/1.40  thf('63', plain,
% 1.20/1.40      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 1.20/1.40         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.20/1.40      inference('demod', [status(thm)], ['61', '62'])).
% 1.20/1.40  thf(t7_ordinal1, axiom,
% 1.20/1.40    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.20/1.40  thf('64', plain,
% 1.20/1.40      (![X71 : $i, X72 : $i]:
% 1.20/1.40         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 1.20/1.40      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.20/1.40  thf('65', plain,
% 1.20/1.40      ((((r2_hidden @ sk_A @ sk_B) | ~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)))
% 1.20/1.40         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['63', '64'])).
% 1.20/1.40  thf('66', plain,
% 1.20/1.40      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | 
% 1.20/1.40       ((r1_ordinal1 @ sk_A @ sk_B))),
% 1.20/1.40      inference('split', [status(esa)], ['21'])).
% 1.20/1.40  thf('67', plain, (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.20/1.40      inference('sat_resolution*', [status(thm)], ['2', '42', '66'])).
% 1.20/1.40  thf('68', plain,
% 1.20/1.40      (((r2_hidden @ sk_A @ sk_B) | ~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A))),
% 1.20/1.40      inference('simpl_trail', [status(thm)], ['65', '67'])).
% 1.20/1.40  thf('69', plain,
% 1.20/1.40      ((~ (v3_ordinal1 @ sk_B)
% 1.20/1.40        | (r1_ordinal1 @ sk_A @ sk_B)
% 1.20/1.40        | ~ (v3_ordinal1 @ sk_A)
% 1.20/1.40        | (r2_hidden @ sk_A @ sk_B))),
% 1.20/1.40      inference('sup-', [status(thm)], ['55', '68'])).
% 1.20/1.40  thf('70', plain, ((v3_ordinal1 @ sk_B)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('71', plain, ((v3_ordinal1 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('72', plain, (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 1.20/1.40      inference('demod', [status(thm)], ['69', '70', '71'])).
% 1.20/1.40  thf('73', plain, (~ (r1_ordinal1 @ sk_A @ sk_B)),
% 1.20/1.40      inference('simpl_trail', [status(thm)], ['1', '43'])).
% 1.20/1.40  thf('74', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.20/1.40      inference('clc', [status(thm)], ['72', '73'])).
% 1.20/1.40  thf('75', plain,
% 1.20/1.40      (![X71 : $i, X72 : $i]:
% 1.20/1.40         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 1.20/1.40      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.20/1.40  thf('76', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 1.20/1.40      inference('sup-', [status(thm)], ['74', '75'])).
% 1.20/1.40  thf('77', plain, ((~ (v3_ordinal1 @ sk_B) | (r1_ordinal1 @ sk_A @ sk_B))),
% 1.20/1.40      inference('sup-', [status(thm)], ['52', '76'])).
% 1.20/1.40  thf('78', plain, ((v3_ordinal1 @ sk_B)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('79', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 1.20/1.40      inference('demod', [status(thm)], ['77', '78'])).
% 1.20/1.40  thf('80', plain, ($false), inference('demod', [status(thm)], ['44', '79'])).
% 1.20/1.40  
% 1.20/1.40  % SZS output end Refutation
% 1.20/1.40  
% 1.20/1.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
