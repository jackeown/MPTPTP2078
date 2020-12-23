%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KJnIyTcx42

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:04 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 176 expanded)
%              Number of leaves         :   23 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :  778 (1414 expanded)
%              Number of equality atoms :   31 (  46 expanded)
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

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

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

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

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
    ! [X69: $i] :
      ( ( k1_ordinal1 @ X69 )
      = ( k2_xboole_0 @ X69 @ ( k1_tarski @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X42 @ X43 ) )
      = ( k2_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X69: $i] :
      ( ( k1_ordinal1 @ X69 )
      = ( k3_tarski @ ( k2_tarski @ X69 @ ( k1_tarski @ X69 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('8',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X42 @ X43 ) )
      = ( k2_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('10',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( X12 = X9 )
      | ( X11
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12 = X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ( sk_A = sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X70: $i,X71: $i] :
      ( ~ ( r2_hidden @ X70 @ X71 )
      | ( r1_tarski @ X70 @ X71 )
      | ~ ( v1_ordinal1 @ X71 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('17',plain,
    ( ( ( sk_A = sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('19',plain,(
    ! [X66: $i] :
      ( ( v1_ordinal1 @ X66 )
      | ~ ( v3_ordinal1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('20',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X73: $i,X74: $i] :
      ( ~ ( v3_ordinal1 @ X73 )
      | ~ ( v3_ordinal1 @ X74 )
      | ( r1_ordinal1 @ X73 @ X74 )
      | ~ ( r1_tarski @ X73 @ X74 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('23',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ( sk_A = sk_B_1 )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('32',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( v3_ordinal1 @ X75 )
      | ( r1_ordinal1 @ X76 @ X75 )
      | ( r2_hidden @ X75 @ X76 )
      | ~ ( v3_ordinal1 @ X76 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('33',plain,(
    ! [X70: $i,X71: $i] :
      ( ~ ( r2_hidden @ X70 @ X71 )
      | ( r1_tarski @ X70 @ X71 )
      | ~ ( v1_ordinal1 @ X71 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X73: $i,X74: $i] :
      ( ~ ( v3_ordinal1 @ X73 )
      | ~ ( v3_ordinal1 @ X74 )
      | ( r1_ordinal1 @ X73 @ X74 )
      | ~ ( r1_tarski @ X73 @ X74 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X66: $i] :
      ( ( v1_ordinal1 @ X66 )
      | ~ ( v3_ordinal1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('41',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference(eq_fact,[status(thm)],['42'])).

thf('44',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r1_ordinal1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','45'])).

thf('47',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('48',plain,(
    ! [X69: $i] :
      ( ( k1_ordinal1 @ X69 )
      = ( k3_tarski @ ( k2_tarski @ X69 @ ( k1_tarski @ X69 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('49',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( v3_ordinal1 @ X75 )
      | ( r1_ordinal1 @ X76 @ X75 )
      | ( r2_hidden @ X75 @ X76 )
      | ~ ( v3_ordinal1 @ X76 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X42 @ X43 ) )
      = ( k2_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k3_tarski @ ( k2_tarski @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r1_ordinal1 @ sk_B_1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( r1_ordinal1 @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X73: $i,X74: $i] :
      ( ~ ( v3_ordinal1 @ X73 )
      | ~ ( v3_ordinal1 @ X74 )
      | ( r1_tarski @ X73 @ X74 )
      | ~ ( r1_ordinal1 @ X73 @ X74 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('62',plain,
    ( ( ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('67',plain,(
    ! [X73: $i,X74: $i] :
      ( ~ ( v3_ordinal1 @ X73 )
      | ~ ( v3_ordinal1 @ X74 )
      | ( r1_tarski @ X73 @ X74 )
      | ~ ( r1_ordinal1 @ X73 @ X74 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('68',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('72',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ( sk_B_1 = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_B_1 = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['65','73'])).

thf('75',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X69: $i] :
      ( ( k1_ordinal1 @ X69 )
      = ( k3_tarski @ ( k2_tarski @ X69 @ ( k1_tarski @ X69 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('78',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X10 != X9 )
      | ( r2_hidden @ X10 @ X11 )
      | ( X11
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('79',plain,(
    ! [X9: $i] :
      ( r2_hidden @ X9 @ ( k1_tarski @ X9 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X42 @ X43 ) )
      = ( k2_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['79','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','84'])).

thf('86',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['76','85'])).

thf('87',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','46','47','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KJnIyTcx42
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.77/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.96  % Solved by: fo/fo7.sh
% 0.77/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.96  % done 1162 iterations in 0.514s
% 0.77/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.96  % SZS output start Refutation
% 0.77/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.96  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.77/0.96  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.77/0.96  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.77/0.96  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.77/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.96  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.77/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/0.96  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.77/0.96  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.77/0.96  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.77/0.96  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.77/0.96  thf(t34_ordinal1, conjecture,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( v3_ordinal1 @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( v3_ordinal1 @ B ) =>
% 0.77/0.96           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.77/0.96             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.77/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.96    (~( ![A:$i]:
% 0.77/0.96        ( ( v3_ordinal1 @ A ) =>
% 0.77/0.96          ( ![B:$i]:
% 0.77/0.96            ( ( v3_ordinal1 @ B ) =>
% 0.77/0.96              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.77/0.96                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.77/0.96    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.77/0.96  thf('0', plain,
% 0.77/0.96      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)
% 0.77/0.96        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('1', plain,
% 0.77/0.96      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.77/0.96       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.77/0.96      inference('split', [status(esa)], ['0'])).
% 0.77/0.96  thf('2', plain,
% 0.77/0.96      (((r1_ordinal1 @ sk_A @ sk_B_1)
% 0.77/0.96        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('3', plain,
% 0.77/0.96      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.77/0.96         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.96      inference('split', [status(esa)], ['2'])).
% 0.77/0.96  thf(d1_ordinal1, axiom,
% 0.77/0.96    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.77/0.96  thf('4', plain,
% 0.77/0.96      (![X69 : $i]:
% 0.77/0.96         ((k1_ordinal1 @ X69) = (k2_xboole_0 @ X69 @ (k1_tarski @ X69)))),
% 0.77/0.96      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.77/0.96  thf(l51_zfmisc_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.77/0.96  thf('5', plain,
% 0.77/0.96      (![X42 : $i, X43 : $i]:
% 0.77/0.96         ((k3_tarski @ (k2_tarski @ X42 @ X43)) = (k2_xboole_0 @ X42 @ X43))),
% 0.77/0.96      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.77/0.96  thf('6', plain,
% 0.77/0.96      (![X69 : $i]:
% 0.77/0.96         ((k1_ordinal1 @ X69)
% 0.77/0.96           = (k3_tarski @ (k2_tarski @ X69 @ (k1_tarski @ X69))))),
% 0.77/0.96      inference('demod', [status(thm)], ['4', '5'])).
% 0.77/0.96  thf(d3_xboole_0, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.77/0.96       ( ![D:$i]:
% 0.77/0.96         ( ( r2_hidden @ D @ C ) <=>
% 0.77/0.96           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.77/0.96  thf('7', plain,
% 0.77/0.96      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.77/0.96         (~ (r2_hidden @ X4 @ X2)
% 0.77/0.96          | (r2_hidden @ X4 @ X3)
% 0.77/0.96          | (r2_hidden @ X4 @ X1)
% 0.77/0.96          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.77/0.96      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.77/0.96  thf('8', plain,
% 0.77/0.96      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.77/0.96         ((r2_hidden @ X4 @ X1)
% 0.77/0.96          | (r2_hidden @ X4 @ X3)
% 0.77/0.96          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.77/0.96      inference('simplify', [status(thm)], ['7'])).
% 0.77/0.96  thf('9', plain,
% 0.77/0.96      (![X42 : $i, X43 : $i]:
% 0.77/0.96         ((k3_tarski @ (k2_tarski @ X42 @ X43)) = (k2_xboole_0 @ X42 @ X43))),
% 0.77/0.96      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.77/0.96  thf('10', plain,
% 0.77/0.96      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.77/0.96         ((r2_hidden @ X4 @ X1)
% 0.77/0.96          | (r2_hidden @ X4 @ X3)
% 0.77/0.96          | ~ (r2_hidden @ X4 @ (k3_tarski @ (k2_tarski @ X3 @ X1))))),
% 0.77/0.96      inference('demod', [status(thm)], ['8', '9'])).
% 0.77/0.96  thf('11', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.77/0.96          | (r2_hidden @ X1 @ X0)
% 0.77/0.96          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['6', '10'])).
% 0.77/0.96  thf('12', plain,
% 0.77/0.96      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))
% 0.77/0.96         | (r2_hidden @ sk_A @ sk_B_1)))
% 0.77/0.96         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['3', '11'])).
% 0.77/0.96  thf(d1_tarski, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.77/0.96       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.77/0.96  thf('13', plain,
% 0.77/0.96      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.77/0.96         (~ (r2_hidden @ X12 @ X11)
% 0.77/0.96          | ((X12) = (X9))
% 0.77/0.96          | ((X11) != (k1_tarski @ X9)))),
% 0.77/0.96      inference('cnf', [status(esa)], [d1_tarski])).
% 0.77/0.96  thf('14', plain,
% 0.77/0.96      (![X9 : $i, X12 : $i]:
% 0.77/0.96         (((X12) = (X9)) | ~ (r2_hidden @ X12 @ (k1_tarski @ X9)))),
% 0.77/0.96      inference('simplify', [status(thm)], ['13'])).
% 0.77/0.96  thf('15', plain,
% 0.77/0.96      ((((r2_hidden @ sk_A @ sk_B_1) | ((sk_A) = (sk_B_1))))
% 0.77/0.96         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['12', '14'])).
% 0.77/0.96  thf(d2_ordinal1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( v1_ordinal1 @ A ) <=>
% 0.77/0.96       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.77/0.96  thf('16', plain,
% 0.77/0.96      (![X70 : $i, X71 : $i]:
% 0.77/0.96         (~ (r2_hidden @ X70 @ X71)
% 0.77/0.96          | (r1_tarski @ X70 @ X71)
% 0.77/0.96          | ~ (v1_ordinal1 @ X71))),
% 0.77/0.96      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.77/0.96  thf('17', plain,
% 0.77/0.96      (((((sk_A) = (sk_B_1))
% 0.77/0.96         | ~ (v1_ordinal1 @ sk_B_1)
% 0.77/0.96         | (r1_tarski @ sk_A @ sk_B_1)))
% 0.77/0.96         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['15', '16'])).
% 0.77/0.96  thf('18', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(cc1_ordinal1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.77/0.96  thf('19', plain,
% 0.77/0.96      (![X66 : $i]: ((v1_ordinal1 @ X66) | ~ (v3_ordinal1 @ X66))),
% 0.77/0.96      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.77/0.96  thf('20', plain, ((v1_ordinal1 @ sk_B_1)),
% 0.77/0.96      inference('sup-', [status(thm)], ['18', '19'])).
% 0.77/0.96  thf('21', plain,
% 0.77/0.96      (((((sk_A) = (sk_B_1)) | (r1_tarski @ sk_A @ sk_B_1)))
% 0.77/0.96         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.96      inference('demod', [status(thm)], ['17', '20'])).
% 0.77/0.96  thf(redefinition_r1_ordinal1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.77/0.96       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.77/0.96  thf('22', plain,
% 0.77/0.96      (![X73 : $i, X74 : $i]:
% 0.77/0.96         (~ (v3_ordinal1 @ X73)
% 0.77/0.96          | ~ (v3_ordinal1 @ X74)
% 0.77/0.96          | (r1_ordinal1 @ X73 @ X74)
% 0.77/0.96          | ~ (r1_tarski @ X73 @ X74))),
% 0.77/0.96      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.77/0.96  thf('23', plain,
% 0.77/0.96      (((((sk_A) = (sk_B_1))
% 0.77/0.96         | (r1_ordinal1 @ sk_A @ sk_B_1)
% 0.77/0.96         | ~ (v3_ordinal1 @ sk_B_1)
% 0.77/0.96         | ~ (v3_ordinal1 @ sk_A)))
% 0.77/0.96         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['21', '22'])).
% 0.77/0.96  thf('24', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('25', plain, ((v3_ordinal1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('26', plain,
% 0.77/0.96      (((((sk_A) = (sk_B_1)) | (r1_ordinal1 @ sk_A @ sk_B_1)))
% 0.77/0.96         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.96      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.77/0.96  thf('27', plain,
% 0.77/0.96      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.77/0.96      inference('split', [status(esa)], ['0'])).
% 0.77/0.96  thf('28', plain,
% 0.77/0.96      ((((sk_A) = (sk_B_1)))
% 0.77/0.96         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 0.77/0.96             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['26', '27'])).
% 0.77/0.96  thf('29', plain,
% 0.77/0.96      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.77/0.96      inference('split', [status(esa)], ['0'])).
% 0.77/0.96  thf('30', plain,
% 0.77/0.96      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.77/0.96         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 0.77/0.96             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['28', '29'])).
% 0.77/0.96  thf('31', plain, ((v3_ordinal1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(t26_ordinal1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( v3_ordinal1 @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( v3_ordinal1 @ B ) =>
% 0.77/0.96           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.77/0.96  thf('32', plain,
% 0.77/0.96      (![X75 : $i, X76 : $i]:
% 0.77/0.96         (~ (v3_ordinal1 @ X75)
% 0.77/0.96          | (r1_ordinal1 @ X76 @ X75)
% 0.77/0.96          | (r2_hidden @ X75 @ X76)
% 0.77/0.96          | ~ (v3_ordinal1 @ X76))),
% 0.77/0.96      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.77/0.96  thf('33', plain,
% 0.77/0.96      (![X70 : $i, X71 : $i]:
% 0.77/0.96         (~ (r2_hidden @ X70 @ X71)
% 0.77/0.96          | (r1_tarski @ X70 @ X71)
% 0.77/0.96          | ~ (v1_ordinal1 @ X71))),
% 0.77/0.96      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.77/0.96  thf('34', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v3_ordinal1 @ X0)
% 0.77/0.96          | (r1_ordinal1 @ X0 @ X1)
% 0.77/0.96          | ~ (v3_ordinal1 @ X1)
% 0.77/0.96          | ~ (v1_ordinal1 @ X0)
% 0.77/0.96          | (r1_tarski @ X1 @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['32', '33'])).
% 0.77/0.96  thf('35', plain,
% 0.77/0.96      (![X73 : $i, X74 : $i]:
% 0.77/0.96         (~ (v3_ordinal1 @ X73)
% 0.77/0.96          | ~ (v3_ordinal1 @ X74)
% 0.77/0.96          | (r1_ordinal1 @ X73 @ X74)
% 0.77/0.96          | ~ (r1_tarski @ X73 @ X74))),
% 0.77/0.96      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.77/0.96  thf('36', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v1_ordinal1 @ X0)
% 0.77/0.96          | ~ (v3_ordinal1 @ X1)
% 0.77/0.96          | (r1_ordinal1 @ X0 @ X1)
% 0.77/0.96          | ~ (v3_ordinal1 @ X0)
% 0.77/0.96          | (r1_ordinal1 @ X1 @ X0)
% 0.77/0.96          | ~ (v3_ordinal1 @ X0)
% 0.77/0.96          | ~ (v3_ordinal1 @ X1))),
% 0.77/0.96      inference('sup-', [status(thm)], ['34', '35'])).
% 0.77/0.96  thf('37', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((r1_ordinal1 @ X1 @ X0)
% 0.77/0.96          | ~ (v3_ordinal1 @ X0)
% 0.77/0.96          | (r1_ordinal1 @ X0 @ X1)
% 0.77/0.96          | ~ (v3_ordinal1 @ X1)
% 0.77/0.96          | ~ (v1_ordinal1 @ X0))),
% 0.77/0.96      inference('simplify', [status(thm)], ['36'])).
% 0.77/0.96  thf('38', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (v1_ordinal1 @ sk_A)
% 0.77/0.96          | ~ (v3_ordinal1 @ X0)
% 0.77/0.96          | (r1_ordinal1 @ sk_A @ X0)
% 0.77/0.96          | (r1_ordinal1 @ X0 @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['31', '37'])).
% 0.77/0.96  thf('39', plain, ((v3_ordinal1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('40', plain,
% 0.77/0.96      (![X66 : $i]: ((v1_ordinal1 @ X66) | ~ (v3_ordinal1 @ X66))),
% 0.77/0.96      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.77/0.96  thf('41', plain, ((v1_ordinal1 @ sk_A)),
% 0.77/0.96      inference('sup-', [status(thm)], ['39', '40'])).
% 0.77/0.96  thf('42', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (v3_ordinal1 @ X0)
% 0.77/0.96          | (r1_ordinal1 @ sk_A @ X0)
% 0.77/0.96          | (r1_ordinal1 @ X0 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['38', '41'])).
% 0.77/0.96  thf('43', plain, (((r1_ordinal1 @ sk_A @ sk_A) | ~ (v3_ordinal1 @ sk_A))),
% 0.77/0.96      inference('eq_fact', [status(thm)], ['42'])).
% 0.77/0.96  thf('44', plain, ((v3_ordinal1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('45', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 0.77/0.96      inference('demod', [status(thm)], ['43', '44'])).
% 0.77/0.96  thf('46', plain,
% 0.77/0.96      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.77/0.96       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.77/0.96      inference('demod', [status(thm)], ['30', '45'])).
% 0.77/0.96  thf('47', plain,
% 0.77/0.96      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.77/0.96       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.77/0.96      inference('split', [status(esa)], ['2'])).
% 0.77/0.96  thf('48', plain,
% 0.77/0.96      (![X69 : $i]:
% 0.77/0.96         ((k1_ordinal1 @ X69)
% 0.77/0.96           = (k3_tarski @ (k2_tarski @ X69 @ (k1_tarski @ X69))))),
% 0.77/0.96      inference('demod', [status(thm)], ['4', '5'])).
% 0.77/0.96  thf('49', plain,
% 0.77/0.96      (![X75 : $i, X76 : $i]:
% 0.77/0.96         (~ (v3_ordinal1 @ X75)
% 0.77/0.96          | (r1_ordinal1 @ X76 @ X75)
% 0.77/0.96          | (r2_hidden @ X75 @ X76)
% 0.77/0.96          | ~ (v3_ordinal1 @ X76))),
% 0.77/0.96      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.77/0.96  thf('50', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.77/0.96         (~ (r2_hidden @ X0 @ X3)
% 0.77/0.96          | (r2_hidden @ X0 @ X2)
% 0.77/0.96          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.77/0.96      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.77/0.96  thf('51', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.77/0.96         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.77/0.96      inference('simplify', [status(thm)], ['50'])).
% 0.77/0.96  thf('52', plain,
% 0.77/0.96      (![X42 : $i, X43 : $i]:
% 0.77/0.96         ((k3_tarski @ (k2_tarski @ X42 @ X43)) = (k2_xboole_0 @ X42 @ X43))),
% 0.77/0.96      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.77/0.96  thf('53', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.77/0.96         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 0.77/0.96          | ~ (r2_hidden @ X0 @ X3))),
% 0.77/0.96      inference('demod', [status(thm)], ['51', '52'])).
% 0.77/0.96  thf('54', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         (~ (v3_ordinal1 @ X0)
% 0.77/0.96          | (r1_ordinal1 @ X0 @ X1)
% 0.77/0.96          | ~ (v3_ordinal1 @ X1)
% 0.77/0.96          | (r2_hidden @ X1 @ (k3_tarski @ (k2_tarski @ X0 @ X2))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['49', '53'])).
% 0.77/0.96  thf('55', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.77/0.96          | ~ (v3_ordinal1 @ X1)
% 0.77/0.96          | (r1_ordinal1 @ X0 @ X1)
% 0.77/0.96          | ~ (v3_ordinal1 @ X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['48', '54'])).
% 0.77/0.96  thf('56', plain,
% 0.77/0.96      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.77/0.96         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.96      inference('split', [status(esa)], ['0'])).
% 0.77/0.96  thf('57', plain,
% 0.77/0.96      (((~ (v3_ordinal1 @ sk_B_1)
% 0.77/0.96         | (r1_ordinal1 @ sk_B_1 @ sk_A)
% 0.77/0.96         | ~ (v3_ordinal1 @ sk_A)))
% 0.77/0.96         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['55', '56'])).
% 0.77/0.96  thf('58', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('59', plain, ((v3_ordinal1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('60', plain,
% 0.77/0.96      (((r1_ordinal1 @ sk_B_1 @ sk_A))
% 0.77/0.96         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.96      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.77/0.96  thf('61', plain,
% 0.77/0.96      (![X73 : $i, X74 : $i]:
% 0.77/0.96         (~ (v3_ordinal1 @ X73)
% 0.77/0.96          | ~ (v3_ordinal1 @ X74)
% 0.77/0.96          | (r1_tarski @ X73 @ X74)
% 0.77/0.96          | ~ (r1_ordinal1 @ X73 @ X74))),
% 0.77/0.96      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.77/0.96  thf('62', plain,
% 0.77/0.96      ((((r1_tarski @ sk_B_1 @ sk_A)
% 0.77/0.96         | ~ (v3_ordinal1 @ sk_A)
% 0.77/0.96         | ~ (v3_ordinal1 @ sk_B_1)))
% 0.77/0.96         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['60', '61'])).
% 0.77/0.96  thf('63', plain, ((v3_ordinal1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('64', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf('65', plain,
% 0.77/0.97      (((r1_tarski @ sk_B_1 @ sk_A))
% 0.77/0.97         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.97      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.77/0.97  thf('66', plain,
% 0.77/0.97      (((r1_ordinal1 @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.77/0.97      inference('split', [status(esa)], ['2'])).
% 0.77/0.97  thf('67', plain,
% 0.77/0.97      (![X73 : $i, X74 : $i]:
% 0.77/0.97         (~ (v3_ordinal1 @ X73)
% 0.77/0.97          | ~ (v3_ordinal1 @ X74)
% 0.77/0.97          | (r1_tarski @ X73 @ X74)
% 0.77/0.97          | ~ (r1_ordinal1 @ X73 @ X74))),
% 0.77/0.97      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.77/0.97  thf('68', plain,
% 0.77/0.97      ((((r1_tarski @ sk_A @ sk_B_1)
% 0.77/0.97         | ~ (v3_ordinal1 @ sk_B_1)
% 0.77/0.97         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['66', '67'])).
% 0.77/0.97  thf('69', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf('70', plain, ((v3_ordinal1 @ sk_A)),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf('71', plain,
% 0.77/0.97      (((r1_tarski @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.77/0.97      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.77/0.97  thf(d10_xboole_0, axiom,
% 0.77/0.97    (![A:$i,B:$i]:
% 0.77/0.97     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.77/0.97  thf('72', plain,
% 0.77/0.97      (![X6 : $i, X8 : $i]:
% 0.77/0.97         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.77/0.97      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/0.97  thf('73', plain,
% 0.77/0.97      (((~ (r1_tarski @ sk_B_1 @ sk_A) | ((sk_B_1) = (sk_A))))
% 0.77/0.97         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['71', '72'])).
% 0.77/0.97  thf('74', plain,
% 0.77/0.97      ((((sk_B_1) = (sk_A)))
% 0.77/0.97         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 0.77/0.97             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['65', '73'])).
% 0.77/0.97  thf('75', plain,
% 0.77/0.97      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.77/0.97         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.77/0.97      inference('split', [status(esa)], ['0'])).
% 0.77/0.97  thf('76', plain,
% 0.77/0.97      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.77/0.97         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 0.77/0.97             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['74', '75'])).
% 0.77/0.97  thf('77', plain,
% 0.77/0.97      (![X69 : $i]:
% 0.77/0.97         ((k1_ordinal1 @ X69)
% 0.77/0.97           = (k3_tarski @ (k2_tarski @ X69 @ (k1_tarski @ X69))))),
% 0.77/0.97      inference('demod', [status(thm)], ['4', '5'])).
% 0.77/0.97  thf('78', plain,
% 0.77/0.97      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.77/0.97         (((X10) != (X9))
% 0.77/0.97          | (r2_hidden @ X10 @ X11)
% 0.77/0.97          | ((X11) != (k1_tarski @ X9)))),
% 0.77/0.97      inference('cnf', [status(esa)], [d1_tarski])).
% 0.77/0.97  thf('79', plain, (![X9 : $i]: (r2_hidden @ X9 @ (k1_tarski @ X9))),
% 0.77/0.97      inference('simplify', [status(thm)], ['78'])).
% 0.77/0.97  thf('80', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.77/0.97         (~ (r2_hidden @ X0 @ X1)
% 0.77/0.97          | (r2_hidden @ X0 @ X2)
% 0.77/0.97          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.77/0.97      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.77/0.97  thf('81', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.77/0.97         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.77/0.97      inference('simplify', [status(thm)], ['80'])).
% 0.77/0.97  thf('82', plain,
% 0.77/0.97      (![X42 : $i, X43 : $i]:
% 0.77/0.97         ((k3_tarski @ (k2_tarski @ X42 @ X43)) = (k2_xboole_0 @ X42 @ X43))),
% 0.77/0.97      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.77/0.97  thf('83', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.77/0.97         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 0.77/0.97          | ~ (r2_hidden @ X0 @ X1))),
% 0.77/0.97      inference('demod', [status(thm)], ['81', '82'])).
% 0.77/0.97  thf('84', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i]:
% 0.77/0.97         (r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ (k1_tarski @ X0))))),
% 0.77/0.97      inference('sup-', [status(thm)], ['79', '83'])).
% 0.77/0.97  thf('85', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 0.77/0.97      inference('sup+', [status(thm)], ['77', '84'])).
% 0.77/0.97  thf('86', plain,
% 0.77/0.97      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.77/0.97       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.77/0.97      inference('demod', [status(thm)], ['76', '85'])).
% 0.77/0.97  thf('87', plain, ($false),
% 0.77/0.97      inference('sat_resolution*', [status(thm)], ['1', '46', '47', '86'])).
% 0.77/0.97  
% 0.77/0.97  % SZS output end Refutation
% 0.77/0.97  
% 0.77/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
