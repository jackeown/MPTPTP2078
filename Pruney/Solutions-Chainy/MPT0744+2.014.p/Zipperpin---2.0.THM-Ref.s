%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o5ildCnhek

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:01 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 160 expanded)
%              Number of leaves         :   20 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  706 (1306 expanded)
%              Number of equality atoms :   29 (  44 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('2',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('4',plain,(
    ! [X68: $i] :
      ( ( k1_ordinal1 @ X68 )
      = ( k2_xboole_0 @ X68 @ ( k1_tarski @ X68 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t93_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t93_zfmisc_1])).

thf('6',plain,(
    ! [X68: $i] :
      ( ( k1_ordinal1 @ X68 )
      = ( k3_tarski @ ( k2_tarski @ X68 @ ( k1_tarski @ X68 ) ) ) ) ),
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
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('8',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t93_zfmisc_1])).

thf('10',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k3_tarski @ ( k2_tarski @ X5 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( X14 = X11 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('16',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( v3_ordinal1 @ X71 )
      | ( r1_ordinal1 @ X72 @ X71 )
      | ( r2_hidden @ X71 @ X72 )
      | ~ ( v3_ordinal1 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( sk_A = sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( v3_ordinal1 @ X71 )
      | ( r1_ordinal1 @ X72 @ X71 )
      | ( r2_hidden @ X71 @ X72 )
      | ~ ( v3_ordinal1 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference(eq_fact,[status(thm)],['32'])).

thf('34',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_ordinal1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','35'])).

thf('37',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('38',plain,(
    ! [X68: $i] :
      ( ( k1_ordinal1 @ X68 )
      = ( k3_tarski @ ( k2_tarski @ X68 @ ( k1_tarski @ X68 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('39',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( v3_ordinal1 @ X71 )
      | ( r1_ordinal1 @ X72 @ X71 )
      | ( r2_hidden @ X71 @ X72 )
      | ~ ( v3_ordinal1 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('40',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('41',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t93_zfmisc_1])).

thf('43',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k3_tarski @ ( k2_tarski @ X5 @ X3 ) ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k3_tarski @ ( k2_tarski @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( v3_ordinal1 @ X69 )
      | ~ ( v3_ordinal1 @ X70 )
      | ( r1_tarski @ X69 @ X70 )
      | ~ ( r1_ordinal1 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('52',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('57',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( v3_ordinal1 @ X69 )
      | ~ ( v3_ordinal1 @ X70 )
      | ( r1_tarski @ X69 @ X70 )
      | ~ ( r1_ordinal1 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('58',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('62',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','63'])).

thf('65',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X68: $i] :
      ( ( k1_ordinal1 @ X68 )
      = ( k3_tarski @ ( k2_tarski @ X68 @ ( k1_tarski @ X68 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('68',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X12 != X11 )
      | ( r2_hidden @ X12 @ X13 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('69',plain,(
    ! [X11: $i] :
      ( r2_hidden @ X11 @ ( k1_tarski @ X11 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('71',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t93_zfmisc_1])).

thf('73',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k3_tarski @ ( k2_tarski @ X5 @ X3 ) ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','74'])).

thf('76',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','75'])).

thf('77',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','36','37','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o5ildCnhek
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:23:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.14/1.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.14/1.32  % Solved by: fo/fo7.sh
% 1.14/1.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.14/1.32  % done 1732 iterations in 0.862s
% 1.14/1.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.14/1.32  % SZS output start Refutation
% 1.14/1.32  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.14/1.32  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.14/1.32  thf(sk_A_type, type, sk_A: $i).
% 1.14/1.32  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 1.14/1.32  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.14/1.32  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 1.14/1.32  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.14/1.32  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.14/1.32  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 1.14/1.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.14/1.32  thf(sk_B_type, type, sk_B: $i).
% 1.14/1.32  thf(t34_ordinal1, conjecture,
% 1.14/1.32    (![A:$i]:
% 1.14/1.32     ( ( v3_ordinal1 @ A ) =>
% 1.14/1.32       ( ![B:$i]:
% 1.14/1.32         ( ( v3_ordinal1 @ B ) =>
% 1.14/1.32           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 1.14/1.32             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 1.14/1.32  thf(zf_stmt_0, negated_conjecture,
% 1.14/1.32    (~( ![A:$i]:
% 1.14/1.32        ( ( v3_ordinal1 @ A ) =>
% 1.14/1.32          ( ![B:$i]:
% 1.14/1.32            ( ( v3_ordinal1 @ B ) =>
% 1.14/1.32              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 1.14/1.32                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 1.14/1.32    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 1.14/1.32  thf('0', plain,
% 1.14/1.32      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 1.14/1.32        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('1', plain,
% 1.14/1.32      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 1.14/1.32       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.14/1.32      inference('split', [status(esa)], ['0'])).
% 1.14/1.32  thf('2', plain,
% 1.14/1.32      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('3', plain,
% 1.14/1.32      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 1.14/1.32         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.14/1.32      inference('split', [status(esa)], ['2'])).
% 1.14/1.32  thf(d1_ordinal1, axiom,
% 1.14/1.32    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 1.14/1.32  thf('4', plain,
% 1.14/1.32      (![X68 : $i]:
% 1.14/1.32         ((k1_ordinal1 @ X68) = (k2_xboole_0 @ X68 @ (k1_tarski @ X68)))),
% 1.14/1.32      inference('cnf', [status(esa)], [d1_ordinal1])).
% 1.14/1.32  thf(t93_zfmisc_1, axiom,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.14/1.32  thf('5', plain,
% 1.14/1.32      (![X44 : $i, X45 : $i]:
% 1.14/1.32         ((k3_tarski @ (k2_tarski @ X44 @ X45)) = (k2_xboole_0 @ X44 @ X45))),
% 1.14/1.32      inference('cnf', [status(esa)], [t93_zfmisc_1])).
% 1.14/1.32  thf('6', plain,
% 1.14/1.32      (![X68 : $i]:
% 1.14/1.32         ((k1_ordinal1 @ X68)
% 1.14/1.32           = (k3_tarski @ (k2_tarski @ X68 @ (k1_tarski @ X68))))),
% 1.14/1.32      inference('demod', [status(thm)], ['4', '5'])).
% 1.14/1.32  thf(d3_xboole_0, axiom,
% 1.14/1.32    (![A:$i,B:$i,C:$i]:
% 1.14/1.32     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.14/1.32       ( ![D:$i]:
% 1.14/1.32         ( ( r2_hidden @ D @ C ) <=>
% 1.14/1.32           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.14/1.32  thf('7', plain,
% 1.14/1.32      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.14/1.32         (~ (r2_hidden @ X6 @ X4)
% 1.14/1.32          | (r2_hidden @ X6 @ X5)
% 1.14/1.32          | (r2_hidden @ X6 @ X3)
% 1.14/1.32          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 1.14/1.32      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.14/1.32  thf('8', plain,
% 1.14/1.32      (![X3 : $i, X5 : $i, X6 : $i]:
% 1.14/1.32         ((r2_hidden @ X6 @ X3)
% 1.14/1.32          | (r2_hidden @ X6 @ X5)
% 1.14/1.32          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 1.14/1.32      inference('simplify', [status(thm)], ['7'])).
% 1.14/1.32  thf('9', plain,
% 1.14/1.32      (![X44 : $i, X45 : $i]:
% 1.14/1.32         ((k3_tarski @ (k2_tarski @ X44 @ X45)) = (k2_xboole_0 @ X44 @ X45))),
% 1.14/1.32      inference('cnf', [status(esa)], [t93_zfmisc_1])).
% 1.14/1.32  thf('10', plain,
% 1.14/1.32      (![X3 : $i, X5 : $i, X6 : $i]:
% 1.14/1.32         ((r2_hidden @ X6 @ X3)
% 1.14/1.32          | (r2_hidden @ X6 @ X5)
% 1.14/1.32          | ~ (r2_hidden @ X6 @ (k3_tarski @ (k2_tarski @ X5 @ X3))))),
% 1.14/1.32      inference('demod', [status(thm)], ['8', '9'])).
% 1.14/1.32  thf('11', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]:
% 1.14/1.32         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 1.14/1.32          | (r2_hidden @ X1 @ X0)
% 1.14/1.32          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.14/1.32      inference('sup-', [status(thm)], ['6', '10'])).
% 1.14/1.32  thf('12', plain,
% 1.14/1.32      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 1.14/1.32         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.14/1.32      inference('sup-', [status(thm)], ['3', '11'])).
% 1.14/1.32  thf(d1_tarski, axiom,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.14/1.32       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.14/1.32  thf('13', plain,
% 1.14/1.32      (![X11 : $i, X13 : $i, X14 : $i]:
% 1.14/1.32         (~ (r2_hidden @ X14 @ X13)
% 1.14/1.32          | ((X14) = (X11))
% 1.14/1.32          | ((X13) != (k1_tarski @ X11)))),
% 1.14/1.32      inference('cnf', [status(esa)], [d1_tarski])).
% 1.14/1.32  thf('14', plain,
% 1.14/1.32      (![X11 : $i, X14 : $i]:
% 1.14/1.32         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 1.14/1.32      inference('simplify', [status(thm)], ['13'])).
% 1.14/1.32  thf('15', plain,
% 1.14/1.32      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 1.14/1.32         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.14/1.32      inference('sup-', [status(thm)], ['12', '14'])).
% 1.14/1.32  thf(t26_ordinal1, axiom,
% 1.14/1.32    (![A:$i]:
% 1.14/1.32     ( ( v3_ordinal1 @ A ) =>
% 1.14/1.32       ( ![B:$i]:
% 1.14/1.32         ( ( v3_ordinal1 @ B ) =>
% 1.14/1.32           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 1.14/1.32  thf('16', plain,
% 1.14/1.32      (![X71 : $i, X72 : $i]:
% 1.14/1.32         (~ (v3_ordinal1 @ X71)
% 1.14/1.32          | (r1_ordinal1 @ X72 @ X71)
% 1.14/1.32          | (r2_hidden @ X71 @ X72)
% 1.14/1.32          | ~ (v3_ordinal1 @ X72))),
% 1.14/1.32      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.14/1.32  thf(antisymmetry_r2_hidden, axiom,
% 1.14/1.32    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 1.14/1.32  thf('17', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 1.14/1.32      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 1.14/1.32  thf('18', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]:
% 1.14/1.32         (~ (v3_ordinal1 @ X0)
% 1.14/1.32          | (r1_ordinal1 @ X0 @ X1)
% 1.14/1.32          | ~ (v3_ordinal1 @ X1)
% 1.14/1.32          | ~ (r2_hidden @ X0 @ X1))),
% 1.14/1.32      inference('sup-', [status(thm)], ['16', '17'])).
% 1.14/1.32  thf('19', plain,
% 1.14/1.32      (((((sk_A) = (sk_B))
% 1.14/1.32         | ~ (v3_ordinal1 @ sk_B)
% 1.14/1.32         | (r1_ordinal1 @ sk_A @ sk_B)
% 1.14/1.32         | ~ (v3_ordinal1 @ sk_A)))
% 1.14/1.32         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.14/1.32      inference('sup-', [status(thm)], ['15', '18'])).
% 1.14/1.32  thf('20', plain, ((v3_ordinal1 @ sk_B)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('21', plain, ((v3_ordinal1 @ sk_A)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('22', plain,
% 1.14/1.32      (((((sk_A) = (sk_B)) | (r1_ordinal1 @ sk_A @ sk_B)))
% 1.14/1.32         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.14/1.32      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.14/1.32  thf('23', plain,
% 1.14/1.32      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.14/1.32      inference('split', [status(esa)], ['0'])).
% 1.14/1.32  thf('24', plain,
% 1.14/1.32      ((((sk_A) = (sk_B)))
% 1.14/1.32         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 1.14/1.32             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.14/1.32      inference('sup-', [status(thm)], ['22', '23'])).
% 1.14/1.32  thf('25', plain,
% 1.14/1.32      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.14/1.32      inference('split', [status(esa)], ['0'])).
% 1.14/1.32  thf('26', plain,
% 1.14/1.32      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 1.14/1.32         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 1.14/1.32             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.14/1.32      inference('sup-', [status(thm)], ['24', '25'])).
% 1.14/1.32  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('28', plain,
% 1.14/1.32      (![X71 : $i, X72 : $i]:
% 1.14/1.32         (~ (v3_ordinal1 @ X71)
% 1.14/1.32          | (r1_ordinal1 @ X72 @ X71)
% 1.14/1.32          | (r2_hidden @ X71 @ X72)
% 1.14/1.32          | ~ (v3_ordinal1 @ X72))),
% 1.14/1.32      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.14/1.32  thf('29', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]:
% 1.14/1.32         (~ (v3_ordinal1 @ X0)
% 1.14/1.32          | (r1_ordinal1 @ X0 @ X1)
% 1.14/1.32          | ~ (v3_ordinal1 @ X1)
% 1.14/1.32          | ~ (r2_hidden @ X0 @ X1))),
% 1.14/1.32      inference('sup-', [status(thm)], ['16', '17'])).
% 1.14/1.32  thf('30', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]:
% 1.14/1.32         (~ (v3_ordinal1 @ X0)
% 1.14/1.32          | (r1_ordinal1 @ X0 @ X1)
% 1.14/1.32          | ~ (v3_ordinal1 @ X1)
% 1.14/1.32          | ~ (v3_ordinal1 @ X0)
% 1.14/1.32          | (r1_ordinal1 @ X1 @ X0)
% 1.14/1.32          | ~ (v3_ordinal1 @ X1))),
% 1.14/1.32      inference('sup-', [status(thm)], ['28', '29'])).
% 1.14/1.32  thf('31', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]:
% 1.14/1.32         ((r1_ordinal1 @ X1 @ X0)
% 1.14/1.32          | ~ (v3_ordinal1 @ X1)
% 1.14/1.32          | (r1_ordinal1 @ X0 @ X1)
% 1.14/1.32          | ~ (v3_ordinal1 @ X0))),
% 1.14/1.32      inference('simplify', [status(thm)], ['30'])).
% 1.14/1.32  thf('32', plain,
% 1.14/1.32      (![X0 : $i]:
% 1.14/1.32         (~ (v3_ordinal1 @ X0)
% 1.14/1.32          | (r1_ordinal1 @ X0 @ sk_A)
% 1.14/1.32          | (r1_ordinal1 @ sk_A @ X0))),
% 1.14/1.32      inference('sup-', [status(thm)], ['27', '31'])).
% 1.14/1.32  thf('33', plain, (((r1_ordinal1 @ sk_A @ sk_A) | ~ (v3_ordinal1 @ sk_A))),
% 1.14/1.32      inference('eq_fact', [status(thm)], ['32'])).
% 1.14/1.32  thf('34', plain, ((v3_ordinal1 @ sk_A)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('35', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 1.14/1.32      inference('demod', [status(thm)], ['33', '34'])).
% 1.14/1.32  thf('36', plain,
% 1.14/1.32      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 1.14/1.32       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.14/1.32      inference('demod', [status(thm)], ['26', '35'])).
% 1.14/1.32  thf('37', plain,
% 1.14/1.32      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 1.14/1.32       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.14/1.32      inference('split', [status(esa)], ['2'])).
% 1.14/1.32  thf('38', plain,
% 1.14/1.32      (![X68 : $i]:
% 1.14/1.32         ((k1_ordinal1 @ X68)
% 1.14/1.32           = (k3_tarski @ (k2_tarski @ X68 @ (k1_tarski @ X68))))),
% 1.14/1.32      inference('demod', [status(thm)], ['4', '5'])).
% 1.14/1.32  thf('39', plain,
% 1.14/1.32      (![X71 : $i, X72 : $i]:
% 1.14/1.32         (~ (v3_ordinal1 @ X71)
% 1.14/1.32          | (r1_ordinal1 @ X72 @ X71)
% 1.14/1.32          | (r2_hidden @ X71 @ X72)
% 1.14/1.32          | ~ (v3_ordinal1 @ X72))),
% 1.14/1.32      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.14/1.32  thf('40', plain,
% 1.14/1.32      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.14/1.32         (~ (r2_hidden @ X2 @ X5)
% 1.14/1.32          | (r2_hidden @ X2 @ X4)
% 1.14/1.32          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 1.14/1.32      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.14/1.32  thf('41', plain,
% 1.14/1.32      (![X2 : $i, X3 : $i, X5 : $i]:
% 1.14/1.32         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 1.14/1.32      inference('simplify', [status(thm)], ['40'])).
% 1.14/1.32  thf('42', plain,
% 1.14/1.32      (![X44 : $i, X45 : $i]:
% 1.14/1.32         ((k3_tarski @ (k2_tarski @ X44 @ X45)) = (k2_xboole_0 @ X44 @ X45))),
% 1.14/1.32      inference('cnf', [status(esa)], [t93_zfmisc_1])).
% 1.14/1.32  thf('43', plain,
% 1.14/1.32      (![X2 : $i, X3 : $i, X5 : $i]:
% 1.14/1.32         ((r2_hidden @ X2 @ (k3_tarski @ (k2_tarski @ X5 @ X3)))
% 1.14/1.32          | ~ (r2_hidden @ X2 @ X5))),
% 1.14/1.32      inference('demod', [status(thm)], ['41', '42'])).
% 1.14/1.32  thf('44', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.32         (~ (v3_ordinal1 @ X0)
% 1.14/1.32          | (r1_ordinal1 @ X0 @ X1)
% 1.14/1.32          | ~ (v3_ordinal1 @ X1)
% 1.14/1.32          | (r2_hidden @ X1 @ (k3_tarski @ (k2_tarski @ X0 @ X2))))),
% 1.14/1.32      inference('sup-', [status(thm)], ['39', '43'])).
% 1.14/1.32  thf('45', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]:
% 1.14/1.32         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 1.14/1.32          | ~ (v3_ordinal1 @ X1)
% 1.14/1.32          | (r1_ordinal1 @ X0 @ X1)
% 1.14/1.32          | ~ (v3_ordinal1 @ X0))),
% 1.14/1.32      inference('sup+', [status(thm)], ['38', '44'])).
% 1.14/1.32  thf('46', plain,
% 1.14/1.32      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 1.14/1.32         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.14/1.32      inference('split', [status(esa)], ['0'])).
% 1.14/1.32  thf('47', plain,
% 1.14/1.32      (((~ (v3_ordinal1 @ sk_B)
% 1.14/1.32         | (r1_ordinal1 @ sk_B @ sk_A)
% 1.14/1.32         | ~ (v3_ordinal1 @ sk_A)))
% 1.14/1.32         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.14/1.32      inference('sup-', [status(thm)], ['45', '46'])).
% 1.14/1.32  thf('48', plain, ((v3_ordinal1 @ sk_B)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('49', plain, ((v3_ordinal1 @ sk_A)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('50', plain,
% 1.14/1.32      (((r1_ordinal1 @ sk_B @ sk_A))
% 1.14/1.32         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.14/1.32      inference('demod', [status(thm)], ['47', '48', '49'])).
% 1.14/1.32  thf(redefinition_r1_ordinal1, axiom,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 1.14/1.32       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 1.14/1.32  thf('51', plain,
% 1.14/1.32      (![X69 : $i, X70 : $i]:
% 1.14/1.32         (~ (v3_ordinal1 @ X69)
% 1.14/1.32          | ~ (v3_ordinal1 @ X70)
% 1.14/1.32          | (r1_tarski @ X69 @ X70)
% 1.14/1.32          | ~ (r1_ordinal1 @ X69 @ X70))),
% 1.14/1.32      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.14/1.32  thf('52', plain,
% 1.14/1.32      ((((r1_tarski @ sk_B @ sk_A)
% 1.14/1.32         | ~ (v3_ordinal1 @ sk_A)
% 1.14/1.32         | ~ (v3_ordinal1 @ sk_B)))
% 1.14/1.32         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.14/1.32      inference('sup-', [status(thm)], ['50', '51'])).
% 1.14/1.32  thf('53', plain, ((v3_ordinal1 @ sk_A)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('54', plain, ((v3_ordinal1 @ sk_B)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('55', plain,
% 1.14/1.32      (((r1_tarski @ sk_B @ sk_A))
% 1.14/1.32         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.14/1.32      inference('demod', [status(thm)], ['52', '53', '54'])).
% 1.14/1.32  thf('56', plain,
% 1.14/1.32      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.14/1.32      inference('split', [status(esa)], ['2'])).
% 1.14/1.32  thf('57', plain,
% 1.14/1.32      (![X69 : $i, X70 : $i]:
% 1.14/1.32         (~ (v3_ordinal1 @ X69)
% 1.14/1.32          | ~ (v3_ordinal1 @ X70)
% 1.14/1.32          | (r1_tarski @ X69 @ X70)
% 1.14/1.32          | ~ (r1_ordinal1 @ X69 @ X70))),
% 1.14/1.32      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.14/1.32  thf('58', plain,
% 1.14/1.32      ((((r1_tarski @ sk_A @ sk_B)
% 1.14/1.32         | ~ (v3_ordinal1 @ sk_B)
% 1.14/1.32         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.14/1.32      inference('sup-', [status(thm)], ['56', '57'])).
% 1.14/1.32  thf('59', plain, ((v3_ordinal1 @ sk_B)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('60', plain, ((v3_ordinal1 @ sk_A)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('61', plain,
% 1.14/1.32      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.14/1.32      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.14/1.32  thf(d10_xboole_0, axiom,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.14/1.32  thf('62', plain,
% 1.14/1.32      (![X8 : $i, X10 : $i]:
% 1.14/1.32         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 1.14/1.32      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.14/1.32  thf('63', plain,
% 1.14/1.32      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A))))
% 1.14/1.32         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.14/1.32      inference('sup-', [status(thm)], ['61', '62'])).
% 1.14/1.32  thf('64', plain,
% 1.14/1.32      ((((sk_B) = (sk_A)))
% 1.14/1.32         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 1.14/1.32             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.14/1.32      inference('sup-', [status(thm)], ['55', '63'])).
% 1.14/1.32  thf('65', plain,
% 1.14/1.32      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 1.14/1.32         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.14/1.32      inference('split', [status(esa)], ['0'])).
% 1.14/1.32  thf('66', plain,
% 1.14/1.32      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 1.14/1.32         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 1.14/1.32             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.14/1.32      inference('sup-', [status(thm)], ['64', '65'])).
% 1.14/1.32  thf('67', plain,
% 1.14/1.32      (![X68 : $i]:
% 1.14/1.32         ((k1_ordinal1 @ X68)
% 1.14/1.32           = (k3_tarski @ (k2_tarski @ X68 @ (k1_tarski @ X68))))),
% 1.14/1.32      inference('demod', [status(thm)], ['4', '5'])).
% 1.14/1.32  thf('68', plain,
% 1.14/1.32      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.14/1.32         (((X12) != (X11))
% 1.14/1.32          | (r2_hidden @ X12 @ X13)
% 1.14/1.32          | ((X13) != (k1_tarski @ X11)))),
% 1.14/1.32      inference('cnf', [status(esa)], [d1_tarski])).
% 1.14/1.32  thf('69', plain, (![X11 : $i]: (r2_hidden @ X11 @ (k1_tarski @ X11))),
% 1.14/1.32      inference('simplify', [status(thm)], ['68'])).
% 1.14/1.32  thf('70', plain,
% 1.14/1.32      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.14/1.32         (~ (r2_hidden @ X2 @ X3)
% 1.14/1.32          | (r2_hidden @ X2 @ X4)
% 1.14/1.32          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 1.14/1.32      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.14/1.32  thf('71', plain,
% 1.14/1.32      (![X2 : $i, X3 : $i, X5 : $i]:
% 1.14/1.32         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 1.14/1.32      inference('simplify', [status(thm)], ['70'])).
% 1.14/1.32  thf('72', plain,
% 1.14/1.32      (![X44 : $i, X45 : $i]:
% 1.14/1.32         ((k3_tarski @ (k2_tarski @ X44 @ X45)) = (k2_xboole_0 @ X44 @ X45))),
% 1.14/1.32      inference('cnf', [status(esa)], [t93_zfmisc_1])).
% 1.14/1.32  thf('73', plain,
% 1.14/1.32      (![X2 : $i, X3 : $i, X5 : $i]:
% 1.14/1.32         ((r2_hidden @ X2 @ (k3_tarski @ (k2_tarski @ X5 @ X3)))
% 1.14/1.32          | ~ (r2_hidden @ X2 @ X3))),
% 1.14/1.32      inference('demod', [status(thm)], ['71', '72'])).
% 1.14/1.32  thf('74', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]:
% 1.14/1.32         (r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ (k1_tarski @ X0))))),
% 1.14/1.32      inference('sup-', [status(thm)], ['69', '73'])).
% 1.14/1.32  thf('75', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 1.14/1.32      inference('sup+', [status(thm)], ['67', '74'])).
% 1.14/1.32  thf('76', plain,
% 1.14/1.32      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 1.14/1.32       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.14/1.32      inference('demod', [status(thm)], ['66', '75'])).
% 1.14/1.32  thf('77', plain, ($false),
% 1.14/1.32      inference('sat_resolution*', [status(thm)], ['1', '36', '37', '76'])).
% 1.14/1.32  
% 1.14/1.32  % SZS output end Refutation
% 1.14/1.32  
% 1.14/1.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
