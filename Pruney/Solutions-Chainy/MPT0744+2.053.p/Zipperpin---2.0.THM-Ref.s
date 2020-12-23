%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y0oNQZZ8C6

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:07 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 199 expanded)
%              Number of leaves         :   28 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  959 (1649 expanded)
%              Number of equality atoms :   47 (  66 expanded)
%              Maximal formula depth    :   13 (   6 average)

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

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

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

thf('2',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X70: $i,X71: $i] :
      ( ~ ( v3_ordinal1 @ X70 )
      | ~ ( v3_ordinal1 @ X71 )
      | ( r1_ordinal1 @ X70 @ X71 )
      | ( r1_ordinal1 @ X71 @ X70 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X73: $i,X74: $i] :
      ( ~ ( v3_ordinal1 @ X73 )
      | ~ ( v3_ordinal1 @ X74 )
      | ( r1_tarski @ X73 @ X74 )
      | ~ ( r1_ordinal1 @ X73 @ X74 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_tarski @ sk_B @ sk_A ) )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( X7 = X8 )
      | ( X7 = X9 )
      | ( X7 = X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('17',plain,(
    ! [X72: $i] :
      ( ( k1_ordinal1 @ X72 )
      = ( k2_xboole_0 @ X72 @ ( k1_tarski @ X72 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X72: $i] :
      ( ( k1_ordinal1 @ X72 )
      = ( k3_tarski @ ( k2_tarski @ X72 @ ( k1_tarski @ X72 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('20',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('21',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('23',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('26',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,
    ( ( ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','32'])).

thf('34',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('35',plain,(
    ! [X79: $i,X80: $i] :
      ( ~ ( r2_hidden @ X79 @ X80 )
      | ~ ( r1_tarski @ X80 @ X79 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('36',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','36'])).

thf('38',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('41',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference(eq_fact,[status(thm)],['40'])).

thf('42',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r1_ordinal1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','43'])).

thf('45',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf('46',plain,(
    ! [X72: $i] :
      ( ( k1_ordinal1 @ X72 )
      = ( k3_tarski @ ( k2_tarski @ X72 @ ( k1_tarski @ X72 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('47',plain,(
    ! [X77: $i,X78: $i] :
      ( ~ ( v3_ordinal1 @ X77 )
      | ( r1_ordinal1 @ X78 @ X77 )
      | ( r2_hidden @ X77 @ X78 )
      | ~ ( v3_ordinal1 @ X78 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k3_tarski @ ( k2_tarski @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','52'])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X73: $i,X74: $i] :
      ( ~ ( v3_ordinal1 @ X73 )
      | ~ ( v3_ordinal1 @ X74 )
      | ( r1_tarski @ X73 @ X74 )
      | ~ ( r1_ordinal1 @ X73 @ X74 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('60',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('65',plain,(
    ! [X73: $i,X74: $i] :
      ( ~ ( v3_ordinal1 @ X73 )
      | ~ ( v3_ordinal1 @ X74 )
      | ( r1_tarski @ X73 @ X74 )
      | ~ ( r1_ordinal1 @ X73 @ X74 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('66',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('70',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( v3_ordinal1 @ X75 )
      | ( r2_hidden @ X76 @ X75 )
      | ( X76 = X75 )
      | ( r2_hidden @ X75 @ X76 )
      | ~ ( v3_ordinal1 @ X76 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('71',plain,(
    ! [X79: $i,X80: $i] :
      ( ~ ( r2_hidden @ X79 @ X80 )
      | ~ ( r1_tarski @ X80 @ X79 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X79: $i,X80: $i] :
      ( ~ ( r2_hidden @ X79 @ X80 )
      | ~ ( r1_tarski @ X80 @ X79 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('78',plain,
    ( ( ( sk_B = sk_A )
      | ~ ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','78'])).

thf('80',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('81',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X72: $i] :
      ( ( k1_ordinal1 @ X72 )
      = ( k3_tarski @ ( k2_tarski @ X72 @ ( k1_tarski @ X72 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('83',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('84',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('85',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( r2_hidden @ X11 @ X15 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('86',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['84','86'])).

thf('88',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X6 )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('89',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ~ ( zip_tseitin_0 @ X6 @ X8 @ X9 @ X6 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['91','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','96'])).

thf('98',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','97'])).

thf('99',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','44','45','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y0oNQZZ8C6
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.80  % Solved by: fo/fo7.sh
% 0.58/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.80  % done 744 iterations in 0.334s
% 0.58/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.80  % SZS output start Refutation
% 0.58/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.80  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.58/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.58/0.80  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.58/0.80  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.58/0.80  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.58/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.80  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.58/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.80  thf(t34_ordinal1, conjecture,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( v3_ordinal1 @ A ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( v3_ordinal1 @ B ) =>
% 0.58/0.80           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.58/0.80             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.58/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.80    (~( ![A:$i]:
% 0.58/0.80        ( ( v3_ordinal1 @ A ) =>
% 0.58/0.80          ( ![B:$i]:
% 0.58/0.80            ( ( v3_ordinal1 @ B ) =>
% 0.58/0.80              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.58/0.80                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.58/0.80    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.58/0.80  thf('0', plain,
% 0.58/0.80      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.58/0.80        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('1', plain,
% 0.58/0.80      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.58/0.80       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.58/0.80      inference('split', [status(esa)], ['0'])).
% 0.58/0.80  thf('2', plain, ((v3_ordinal1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(connectedness_r1_ordinal1, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.58/0.80       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.58/0.80  thf('3', plain,
% 0.58/0.80      (![X70 : $i, X71 : $i]:
% 0.58/0.80         (~ (v3_ordinal1 @ X70)
% 0.58/0.80          | ~ (v3_ordinal1 @ X71)
% 0.58/0.80          | (r1_ordinal1 @ X70 @ X71)
% 0.58/0.80          | (r1_ordinal1 @ X71 @ X70))),
% 0.58/0.80      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.58/0.80  thf('4', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r1_ordinal1 @ X0 @ sk_A)
% 0.58/0.80          | (r1_ordinal1 @ sk_A @ X0)
% 0.58/0.80          | ~ (v3_ordinal1 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.80  thf(redefinition_r1_ordinal1, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.58/0.80       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.58/0.80  thf('5', plain,
% 0.58/0.80      (![X73 : $i, X74 : $i]:
% 0.58/0.80         (~ (v3_ordinal1 @ X73)
% 0.58/0.80          | ~ (v3_ordinal1 @ X74)
% 0.58/0.80          | (r1_tarski @ X73 @ X74)
% 0.58/0.80          | ~ (r1_ordinal1 @ X73 @ X74))),
% 0.58/0.80      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.58/0.80  thf('6', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (v3_ordinal1 @ X0)
% 0.58/0.80          | (r1_ordinal1 @ sk_A @ X0)
% 0.58/0.80          | (r1_tarski @ X0 @ sk_A)
% 0.58/0.80          | ~ (v3_ordinal1 @ sk_A)
% 0.58/0.80          | ~ (v3_ordinal1 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['4', '5'])).
% 0.58/0.80  thf('7', plain, ((v3_ordinal1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('8', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (v3_ordinal1 @ X0)
% 0.58/0.80          | (r1_ordinal1 @ sk_A @ X0)
% 0.58/0.80          | (r1_tarski @ X0 @ sk_A)
% 0.58/0.80          | ~ (v3_ordinal1 @ X0))),
% 0.58/0.80      inference('demod', [status(thm)], ['6', '7'])).
% 0.58/0.80  thf('9', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r1_tarski @ X0 @ sk_A)
% 0.58/0.80          | (r1_ordinal1 @ sk_A @ X0)
% 0.58/0.80          | ~ (v3_ordinal1 @ X0))),
% 0.58/0.80      inference('simplify', [status(thm)], ['8'])).
% 0.58/0.80  thf('10', plain,
% 0.58/0.80      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('split', [status(esa)], ['0'])).
% 0.58/0.80  thf('11', plain,
% 0.58/0.80      (((~ (v3_ordinal1 @ sk_B) | (r1_tarski @ sk_B @ sk_A)))
% 0.58/0.80         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['9', '10'])).
% 0.58/0.80  thf('12', plain, ((v3_ordinal1 @ sk_B)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('13', plain,
% 0.58/0.80      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('demod', [status(thm)], ['11', '12'])).
% 0.58/0.80  thf(d1_enumset1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.80     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.58/0.80       ( ![E:$i]:
% 0.58/0.80         ( ( r2_hidden @ E @ D ) <=>
% 0.58/0.80           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.58/0.80  thf(zf_stmt_1, axiom,
% 0.58/0.80    (![E:$i,C:$i,B:$i,A:$i]:
% 0.58/0.80     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.58/0.80       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.58/0.80  thf('14', plain,
% 0.58/0.80      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.58/0.80         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.58/0.80          | ((X7) = (X8))
% 0.58/0.80          | ((X7) = (X9))
% 0.58/0.80          | ((X7) = (X10)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.80  thf('15', plain,
% 0.58/0.80      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('16', plain,
% 0.58/0.80      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.58/0.80         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.58/0.80      inference('split', [status(esa)], ['15'])).
% 0.58/0.80  thf(d1_ordinal1, axiom,
% 0.58/0.80    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.58/0.80  thf('17', plain,
% 0.58/0.80      (![X72 : $i]:
% 0.58/0.80         ((k1_ordinal1 @ X72) = (k2_xboole_0 @ X72 @ (k1_tarski @ X72)))),
% 0.58/0.80      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.58/0.80  thf(l51_zfmisc_1, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.80  thf('18', plain,
% 0.58/0.80      (![X46 : $i, X47 : $i]:
% 0.58/0.80         ((k3_tarski @ (k2_tarski @ X46 @ X47)) = (k2_xboole_0 @ X46 @ X47))),
% 0.58/0.80      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.80  thf('19', plain,
% 0.58/0.80      (![X72 : $i]:
% 0.58/0.80         ((k1_ordinal1 @ X72)
% 0.58/0.80           = (k3_tarski @ (k2_tarski @ X72 @ (k1_tarski @ X72))))),
% 0.58/0.80      inference('demod', [status(thm)], ['17', '18'])).
% 0.58/0.80  thf(d3_xboole_0, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.58/0.80       ( ![D:$i]:
% 0.58/0.80         ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.80           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.58/0.80  thf('20', plain,
% 0.58/0.80      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X4 @ X2)
% 0.58/0.80          | (r2_hidden @ X4 @ X3)
% 0.58/0.80          | (r2_hidden @ X4 @ X1)
% 0.58/0.80          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.58/0.80      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.58/0.80  thf('21', plain,
% 0.58/0.80      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.58/0.80         ((r2_hidden @ X4 @ X1)
% 0.58/0.80          | (r2_hidden @ X4 @ X3)
% 0.58/0.80          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.58/0.80      inference('simplify', [status(thm)], ['20'])).
% 0.58/0.80  thf('22', plain,
% 0.58/0.80      (![X46 : $i, X47 : $i]:
% 0.58/0.80         ((k3_tarski @ (k2_tarski @ X46 @ X47)) = (k2_xboole_0 @ X46 @ X47))),
% 0.58/0.80      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.80  thf('23', plain,
% 0.58/0.80      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.58/0.80         ((r2_hidden @ X4 @ X1)
% 0.58/0.80          | (r2_hidden @ X4 @ X3)
% 0.58/0.80          | ~ (r2_hidden @ X4 @ (k3_tarski @ (k2_tarski @ X3 @ X1))))),
% 0.58/0.80      inference('demod', [status(thm)], ['21', '22'])).
% 0.58/0.80  thf('24', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.58/0.80          | (r2_hidden @ X1 @ X0)
% 0.58/0.80          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['19', '23'])).
% 0.58/0.80  thf('25', plain,
% 0.58/0.80      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 0.58/0.80         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['16', '24'])).
% 0.58/0.80  thf(t69_enumset1, axiom,
% 0.58/0.80    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.58/0.80  thf('26', plain,
% 0.58/0.80      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.58/0.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.80  thf(t70_enumset1, axiom,
% 0.58/0.80    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.58/0.80  thf('27', plain,
% 0.58/0.80      (![X19 : $i, X20 : $i]:
% 0.58/0.80         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.58/0.80      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.80  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.58/0.80  thf(zf_stmt_3, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.80     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.58/0.80       ( ![E:$i]:
% 0.58/0.80         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.58/0.80  thf('28', plain,
% 0.58/0.80      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X16 @ X15)
% 0.58/0.80          | ~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.58/0.80          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.80  thf('29', plain,
% 0.58/0.80      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.58/0.80         (~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.58/0.80          | ~ (r2_hidden @ X16 @ (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.58/0.80      inference('simplify', [status(thm)], ['28'])).
% 0.58/0.80  thf('30', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.58/0.80          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['27', '29'])).
% 0.58/0.80  thf('31', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.58/0.80          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['26', '30'])).
% 0.58/0.80  thf('32', plain,
% 0.58/0.80      ((((r2_hidden @ sk_A @ sk_B)
% 0.58/0.80         | ~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)))
% 0.58/0.80         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['25', '31'])).
% 0.58/0.80  thf('33', plain,
% 0.58/0.80      (((((sk_A) = (sk_B))
% 0.58/0.80         | ((sk_A) = (sk_B))
% 0.58/0.80         | ((sk_A) = (sk_B))
% 0.58/0.80         | (r2_hidden @ sk_A @ sk_B)))
% 0.58/0.80         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['14', '32'])).
% 0.58/0.80  thf('34', plain,
% 0.58/0.80      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.58/0.80         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.58/0.80      inference('simplify', [status(thm)], ['33'])).
% 0.58/0.80  thf(t7_ordinal1, axiom,
% 0.58/0.80    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.80  thf('35', plain,
% 0.58/0.80      (![X79 : $i, X80 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X79 @ X80) | ~ (r1_tarski @ X80 @ X79))),
% 0.58/0.80      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.58/0.80  thf('36', plain,
% 0.58/0.80      (((((sk_A) = (sk_B)) | ~ (r1_tarski @ sk_B @ sk_A)))
% 0.58/0.80         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['34', '35'])).
% 0.58/0.80  thf('37', plain,
% 0.58/0.80      ((((sk_A) = (sk_B)))
% 0.58/0.80         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.58/0.80             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['13', '36'])).
% 0.58/0.80  thf('38', plain,
% 0.58/0.80      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('split', [status(esa)], ['0'])).
% 0.58/0.80  thf('39', plain,
% 0.58/0.80      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.58/0.80         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.58/0.80             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['37', '38'])).
% 0.58/0.80  thf('40', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r1_ordinal1 @ X0 @ sk_A)
% 0.58/0.80          | (r1_ordinal1 @ sk_A @ X0)
% 0.58/0.80          | ~ (v3_ordinal1 @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.80  thf('41', plain, ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ sk_A))),
% 0.58/0.80      inference('eq_fact', [status(thm)], ['40'])).
% 0.58/0.80  thf('42', plain, ((v3_ordinal1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('43', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 0.58/0.80      inference('demod', [status(thm)], ['41', '42'])).
% 0.58/0.80  thf('44', plain,
% 0.58/0.80      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.58/0.80       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.58/0.80      inference('demod', [status(thm)], ['39', '43'])).
% 0.58/0.80  thf('45', plain,
% 0.58/0.80      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.58/0.80       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.58/0.80      inference('split', [status(esa)], ['15'])).
% 0.58/0.80  thf('46', plain,
% 0.58/0.80      (![X72 : $i]:
% 0.58/0.80         ((k1_ordinal1 @ X72)
% 0.58/0.80           = (k3_tarski @ (k2_tarski @ X72 @ (k1_tarski @ X72))))),
% 0.58/0.80      inference('demod', [status(thm)], ['17', '18'])).
% 0.58/0.80  thf(t26_ordinal1, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( v3_ordinal1 @ A ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( v3_ordinal1 @ B ) =>
% 0.58/0.80           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.58/0.80  thf('47', plain,
% 0.58/0.80      (![X77 : $i, X78 : $i]:
% 0.58/0.80         (~ (v3_ordinal1 @ X77)
% 0.58/0.80          | (r1_ordinal1 @ X78 @ X77)
% 0.58/0.80          | (r2_hidden @ X77 @ X78)
% 0.58/0.80          | ~ (v3_ordinal1 @ X78))),
% 0.58/0.80      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.58/0.80  thf('48', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X0 @ X3)
% 0.58/0.80          | (r2_hidden @ X0 @ X2)
% 0.58/0.80          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.58/0.80      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.58/0.80  thf('49', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.58/0.80         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.58/0.80      inference('simplify', [status(thm)], ['48'])).
% 0.58/0.80  thf('50', plain,
% 0.58/0.80      (![X46 : $i, X47 : $i]:
% 0.58/0.80         ((k3_tarski @ (k2_tarski @ X46 @ X47)) = (k2_xboole_0 @ X46 @ X47))),
% 0.58/0.80      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.80  thf('51', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.58/0.80         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 0.58/0.80          | ~ (r2_hidden @ X0 @ X3))),
% 0.58/0.80      inference('demod', [status(thm)], ['49', '50'])).
% 0.58/0.80  thf('52', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         (~ (v3_ordinal1 @ X0)
% 0.58/0.80          | (r1_ordinal1 @ X0 @ X1)
% 0.58/0.80          | ~ (v3_ordinal1 @ X1)
% 0.58/0.80          | (r2_hidden @ X1 @ (k3_tarski @ (k2_tarski @ X0 @ X2))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['47', '51'])).
% 0.58/0.80  thf('53', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.58/0.80          | ~ (v3_ordinal1 @ X1)
% 0.58/0.80          | (r1_ordinal1 @ X0 @ X1)
% 0.58/0.80          | ~ (v3_ordinal1 @ X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['46', '52'])).
% 0.58/0.80  thf('54', plain,
% 0.58/0.80      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.58/0.80         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.58/0.80      inference('split', [status(esa)], ['0'])).
% 0.58/0.80  thf('55', plain,
% 0.58/0.80      (((~ (v3_ordinal1 @ sk_B)
% 0.58/0.80         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.58/0.80         | ~ (v3_ordinal1 @ sk_A)))
% 0.58/0.80         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['53', '54'])).
% 0.58/0.80  thf('56', plain, ((v3_ordinal1 @ sk_B)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('57', plain, ((v3_ordinal1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('58', plain,
% 0.58/0.80      (((r1_ordinal1 @ sk_B @ sk_A))
% 0.58/0.80         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.58/0.80      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.58/0.80  thf('59', plain,
% 0.58/0.80      (![X73 : $i, X74 : $i]:
% 0.58/0.80         (~ (v3_ordinal1 @ X73)
% 0.58/0.80          | ~ (v3_ordinal1 @ X74)
% 0.58/0.80          | (r1_tarski @ X73 @ X74)
% 0.58/0.80          | ~ (r1_ordinal1 @ X73 @ X74))),
% 0.58/0.80      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.58/0.80  thf('60', plain,
% 0.58/0.80      ((((r1_tarski @ sk_B @ sk_A)
% 0.58/0.80         | ~ (v3_ordinal1 @ sk_A)
% 0.58/0.80         | ~ (v3_ordinal1 @ sk_B)))
% 0.58/0.80         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['58', '59'])).
% 0.58/0.80  thf('61', plain, ((v3_ordinal1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('62', plain, ((v3_ordinal1 @ sk_B)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('63', plain,
% 0.58/0.80      (((r1_tarski @ sk_B @ sk_A))
% 0.58/0.80         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.58/0.80      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.58/0.80  thf('64', plain,
% 0.58/0.80      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('split', [status(esa)], ['15'])).
% 0.58/0.80  thf('65', plain,
% 0.58/0.80      (![X73 : $i, X74 : $i]:
% 0.58/0.80         (~ (v3_ordinal1 @ X73)
% 0.58/0.80          | ~ (v3_ordinal1 @ X74)
% 0.58/0.80          | (r1_tarski @ X73 @ X74)
% 0.58/0.80          | ~ (r1_ordinal1 @ X73 @ X74))),
% 0.58/0.80      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.58/0.80  thf('66', plain,
% 0.58/0.80      ((((r1_tarski @ sk_A @ sk_B)
% 0.58/0.80         | ~ (v3_ordinal1 @ sk_B)
% 0.58/0.80         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['64', '65'])).
% 0.58/0.80  thf('67', plain, ((v3_ordinal1 @ sk_B)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('68', plain, ((v3_ordinal1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('69', plain,
% 0.58/0.80      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.58/0.80  thf(t24_ordinal1, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( v3_ordinal1 @ A ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( v3_ordinal1 @ B ) =>
% 0.58/0.80           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.58/0.80                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.58/0.80  thf('70', plain,
% 0.58/0.80      (![X75 : $i, X76 : $i]:
% 0.58/0.80         (~ (v3_ordinal1 @ X75)
% 0.58/0.80          | (r2_hidden @ X76 @ X75)
% 0.58/0.80          | ((X76) = (X75))
% 0.58/0.80          | (r2_hidden @ X75 @ X76)
% 0.58/0.80          | ~ (v3_ordinal1 @ X76))),
% 0.58/0.80      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.58/0.80  thf('71', plain,
% 0.58/0.80      (![X79 : $i, X80 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X79 @ X80) | ~ (r1_tarski @ X80 @ X79))),
% 0.58/0.80      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.58/0.80  thf('72', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (v3_ordinal1 @ X1)
% 0.58/0.80          | (r2_hidden @ X0 @ X1)
% 0.58/0.80          | ((X1) = (X0))
% 0.58/0.80          | ~ (v3_ordinal1 @ X0)
% 0.58/0.80          | ~ (r1_tarski @ X0 @ X1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['70', '71'])).
% 0.58/0.80  thf('73', plain,
% 0.58/0.80      (((~ (v3_ordinal1 @ sk_A)
% 0.58/0.80         | ((sk_B) = (sk_A))
% 0.58/0.80         | (r2_hidden @ sk_A @ sk_B)
% 0.58/0.80         | ~ (v3_ordinal1 @ sk_B))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['69', '72'])).
% 0.58/0.80  thf('74', plain, ((v3_ordinal1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('75', plain, ((v3_ordinal1 @ sk_B)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('76', plain,
% 0.58/0.80      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B)))
% 0.58/0.80         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.58/0.80  thf('77', plain,
% 0.58/0.80      (![X79 : $i, X80 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X79 @ X80) | ~ (r1_tarski @ X80 @ X79))),
% 0.58/0.80      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.58/0.80  thf('78', plain,
% 0.58/0.80      (((((sk_B) = (sk_A)) | ~ (r1_tarski @ sk_B @ sk_A)))
% 0.58/0.80         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['76', '77'])).
% 0.58/0.80  thf('79', plain,
% 0.58/0.80      ((((sk_B) = (sk_A)))
% 0.58/0.80         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.58/0.80             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['63', '78'])).
% 0.58/0.80  thf('80', plain,
% 0.58/0.80      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.58/0.80         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.58/0.80      inference('split', [status(esa)], ['0'])).
% 0.58/0.80  thf('81', plain,
% 0.58/0.80      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.58/0.80         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.58/0.80             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['79', '80'])).
% 0.58/0.80  thf('82', plain,
% 0.58/0.80      (![X72 : $i]:
% 0.58/0.80         ((k1_ordinal1 @ X72)
% 0.58/0.80           = (k3_tarski @ (k2_tarski @ X72 @ (k1_tarski @ X72))))),
% 0.58/0.80      inference('demod', [status(thm)], ['17', '18'])).
% 0.58/0.80  thf('83', plain,
% 0.58/0.80      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.58/0.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.80  thf('84', plain,
% 0.58/0.80      (![X19 : $i, X20 : $i]:
% 0.58/0.80         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 0.58/0.80      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.80  thf('85', plain,
% 0.58/0.80      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.58/0.80         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 0.58/0.80          | (r2_hidden @ X11 @ X15)
% 0.58/0.80          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.80  thf('86', plain,
% 0.58/0.80      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.58/0.80         ((r2_hidden @ X11 @ (k1_enumset1 @ X14 @ X13 @ X12))
% 0.58/0.80          | (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14))),
% 0.58/0.80      inference('simplify', [status(thm)], ['85'])).
% 0.58/0.80  thf('87', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.58/0.80          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.58/0.80      inference('sup+', [status(thm)], ['84', '86'])).
% 0.58/0.80  thf('88', plain,
% 0.58/0.80      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.58/0.80         (((X7) != (X6)) | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X6))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.80  thf('89', plain,
% 0.58/0.80      (![X6 : $i, X8 : $i, X9 : $i]: ~ (zip_tseitin_0 @ X6 @ X8 @ X9 @ X6)),
% 0.58/0.80      inference('simplify', [status(thm)], ['88'])).
% 0.58/0.80  thf('90', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['87', '89'])).
% 0.58/0.80  thf('91', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['83', '90'])).
% 0.58/0.80  thf('92', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X0 @ X1)
% 0.58/0.80          | (r2_hidden @ X0 @ X2)
% 0.58/0.80          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.58/0.80      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.58/0.80  thf('93', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.58/0.80         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.58/0.80      inference('simplify', [status(thm)], ['92'])).
% 0.58/0.80  thf('94', plain,
% 0.58/0.80      (![X46 : $i, X47 : $i]:
% 0.58/0.80         ((k3_tarski @ (k2_tarski @ X46 @ X47)) = (k2_xboole_0 @ X46 @ X47))),
% 0.58/0.80      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.80  thf('95', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.58/0.80         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 0.58/0.80          | ~ (r2_hidden @ X0 @ X1))),
% 0.58/0.80      inference('demod', [status(thm)], ['93', '94'])).
% 0.58/0.80  thf('96', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ (k1_tarski @ X0))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['91', '95'])).
% 0.58/0.80  thf('97', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['82', '96'])).
% 0.58/0.80  thf('98', plain,
% 0.58/0.80      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.58/0.80       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.58/0.80      inference('demod', [status(thm)], ['81', '97'])).
% 0.58/0.80  thf('99', plain, ($false),
% 0.58/0.80      inference('sat_resolution*', [status(thm)], ['1', '44', '45', '98'])).
% 0.58/0.80  
% 0.58/0.80  % SZS output end Refutation
% 0.58/0.80  
% 0.58/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
