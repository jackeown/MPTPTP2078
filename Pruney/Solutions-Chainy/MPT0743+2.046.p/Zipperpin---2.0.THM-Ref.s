%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.130uISaG5g

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:59 EST 2020

% Result     : Theorem 5.02s
% Output     : Refutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 381 expanded)
%              Number of leaves         :   41 ( 124 expanded)
%              Depth                    :   22
%              Number of atoms          : 1830 (3522 expanded)
%              Number of equality atoms :   82 ( 151 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( v3_ordinal1 @ X61 )
      | ~ ( v3_ordinal1 @ X62 )
      | ( r1_ordinal1 @ X61 @ X62 )
      | ( r1_ordinal1 @ X62 @ X61 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v3_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X65 )
      | ( r1_tarski @ X64 @ X65 )
      | ~ ( r1_ordinal1 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v3_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X65 )
      | ( r1_tarski @ X64 @ X65 )
      | ~ ( r1_ordinal1 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_A @ ( k3_tarski @ ( k2_tarski @ X0 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('17',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('18',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ sk_B ) ) @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k3_tarski @ ( k1_tarski @ sk_B ) ) @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,
    ( ( ~ ( v3_ordinal1 @ ( k3_tarski @ ( k1_tarski @ sk_B ) ) )
      | ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ sk_A @ ( k3_tarski @ ( k1_tarski @ sk_B ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf('21',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('22',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('23',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('24',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X0 )
      | ( X1
        = ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('28',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('29',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('33',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','33'])).

thf('35',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','33'])).

thf('38',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['20','34','35','36','37'])).

thf('39',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('40',plain,(
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X34 ) @ X36 )
      | ~ ( r2_hidden @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('41',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('42',plain,(
    ! [X70: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X70 ) )
      | ~ ( v3_ordinal1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('43',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( v3_ordinal1 @ X68 )
      | ( r1_ordinal1 @ X69 @ X68 )
      | ( r2_hidden @ X68 @ X69 )
      | ~ ( v3_ordinal1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('44',plain,(
    ! [X63: $i] :
      ( ( k1_ordinal1 @ X63 )
      = ( k2_xboole_0 @ X63 @ ( k1_tarski @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('45',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('46',plain,(
    ! [X63: $i] :
      ( ( k1_ordinal1 @ X63 )
      = ( k3_tarski @ ( k2_tarski @ X63 @ ( k1_tarski @ X63 ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('48',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('50',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','52'])).

thf('54',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','55'])).

thf('57',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( r2_hidden @ sk_B @ sk_A )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('63',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','63'])).

thf('65',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('66',plain,(
    ! [X70: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X70 ) )
      | ~ ( v3_ordinal1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('67',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('68',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v3_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X65 )
      | ( r1_tarski @ X64 @ X65 )
      | ~ ( r1_ordinal1 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('69',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('76',plain,(
    ! [X63: $i] :
      ( ( k1_ordinal1 @ X63 )
      = ( k3_tarski @ ( k2_tarski @ X63 @ ( k1_tarski @ X63 ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k3_tarski @ ( k2_tarski @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( v3_ordinal1 @ X68 )
      | ( r1_ordinal1 @ X69 @ X68 )
      | ( r2_hidden @ X68 @ X69 )
      | ~ ( v3_ordinal1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k3_tarski @ ( k2_tarski @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','83'])).

thf('85',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['74','86'])).

thf('88',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v3_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X65 )
      | ( r1_tarski @ X64 @ X65 )
      | ~ ( r1_ordinal1 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('92',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('96',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( v3_ordinal1 @ X66 )
      | ( r2_hidden @ X67 @ X66 )
      | ( X67 = X66 )
      | ( r2_hidden @ X66 @ X67 )
      | ~ ( v3_ordinal1 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('97',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('106',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X70: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X70 ) )
      | ~ ( v3_ordinal1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('108',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( v3_ordinal1 @ X61 )
      | ~ ( v3_ordinal1 @ X62 )
      | ( r1_ordinal1 @ X61 @ X62 )
      | ( r1_ordinal1 @ X62 @ X61 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v3_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X65 )
      | ( r1_tarski @ X64 @ X65 )
      | ~ ( r1_ordinal1 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X70: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X70 ) )
      | ~ ( v3_ordinal1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v3_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X65 )
      | ( r1_tarski @ X64 @ X65 )
      | ~ ( r1_ordinal1 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X70: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X70 ) )
      | ~ ( v3_ordinal1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( ( k1_ordinal1 @ X0 )
        = X0 )
      | ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ( ( k1_ordinal1 @ X0 )
        = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( ( k1_ordinal1 @ X0 )
        = X0 )
      | ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ( ( k1_ordinal1 @ X0 )
        = X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( ( k1_ordinal1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( ( k1_ordinal1 @ sk_A )
        = sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','130'])).

thf('132',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X63: $i] :
      ( ( k1_ordinal1 @ X63 )
      = ( k3_tarski @ ( k2_tarski @ X63 @ ( k1_tarski @ X63 ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('135',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X7 @ X7 @ X8 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('136',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('138',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X9 @ X9 @ X10 @ X11 )
      = ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('139',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('140',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('141',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('142',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k6_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(d6_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( ( J != H )
              & ( J != G )
              & ( J != F )
              & ( J != E )
              & ( J != D )
              & ( J != C )
              & ( J != B )
              & ( J != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [J: $i,H: $i,G: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A )
    <=> ( ( J != A )
        & ( J != B )
        & ( J != C )
        & ( J != D )
        & ( J != E )
        & ( J != F )
        & ( J != G )
        & ( J != H ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('143',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 )
      | ( r2_hidden @ X49 @ X58 )
      | ( X58
       != ( k6_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('144',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( r2_hidden @ X49 @ ( k6_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50 ) )
      | ( zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['142','144'])).

thf('146',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( X40 != X39 )
      | ~ ( zip_tseitin_0 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('147',plain,(
    ! [X39: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ~ ( zip_tseitin_0 @ X39 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X39 ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['145','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['141','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['140','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['139','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['138','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['137','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['134','155'])).

thf('157',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('158',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['133','158'])).

thf('160',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( v3_ordinal1 @ X61 )
      | ~ ( v3_ordinal1 @ X62 )
      | ( r1_ordinal1 @ X61 @ X62 )
      | ( r1_ordinal1 @ X62 @ X61 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference(eq_fact,[status(thm)],['162'])).

thf('164',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    r1_ordinal1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v3_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X65 )
      | ( r1_tarski @ X64 @ X65 )
      | ~ ( r1_ordinal1 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('167',plain,
    ( ( r1_tarski @ sk_A @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    r1_tarski @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['159','170'])).

thf('172',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','64','65','171'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.130uISaG5g
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:10:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 5.02/5.27  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.02/5.27  % Solved by: fo/fo7.sh
% 5.02/5.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.02/5.27  % done 8113 iterations in 4.805s
% 5.02/5.27  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.02/5.27  % SZS output start Refutation
% 5.02/5.27  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.02/5.27  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 5.02/5.27  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 5.02/5.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.02/5.27  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 5.02/5.27  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 5.02/5.27                                               $i > $i > $i > $o).
% 5.02/5.27  thf(sk_A_type, type, sk_A: $i).
% 5.02/5.27  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.02/5.27  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.02/5.27  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.02/5.27  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 5.02/5.27                                           $i > $i).
% 5.02/5.27  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 5.02/5.27  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 5.02/5.27  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.02/5.27  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 5.02/5.27  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 5.02/5.27  thf(sk_B_type, type, sk_B: $i).
% 5.02/5.27  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 5.02/5.27  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 5.02/5.27  thf(t33_ordinal1, conjecture,
% 5.02/5.27    (![A:$i]:
% 5.02/5.27     ( ( v3_ordinal1 @ A ) =>
% 5.02/5.27       ( ![B:$i]:
% 5.02/5.27         ( ( v3_ordinal1 @ B ) =>
% 5.02/5.27           ( ( r2_hidden @ A @ B ) <=>
% 5.02/5.27             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 5.02/5.27  thf(zf_stmt_0, negated_conjecture,
% 5.02/5.27    (~( ![A:$i]:
% 5.02/5.27        ( ( v3_ordinal1 @ A ) =>
% 5.02/5.27          ( ![B:$i]:
% 5.02/5.27            ( ( v3_ordinal1 @ B ) =>
% 5.02/5.27              ( ( r2_hidden @ A @ B ) <=>
% 5.02/5.27                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 5.02/5.27    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 5.02/5.27  thf('0', plain,
% 5.02/5.27      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 5.02/5.27        | ~ (r2_hidden @ sk_A @ sk_B))),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.27  thf('1', plain,
% 5.02/5.27      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 5.02/5.27       ~ ((r2_hidden @ sk_A @ sk_B))),
% 5.02/5.27      inference('split', [status(esa)], ['0'])).
% 5.02/5.27  thf(connectedness_r1_ordinal1, axiom,
% 5.02/5.27    (![A:$i,B:$i]:
% 5.02/5.27     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 5.02/5.27       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 5.02/5.27  thf('2', plain,
% 5.02/5.27      (![X61 : $i, X62 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X61)
% 5.02/5.27          | ~ (v3_ordinal1 @ X62)
% 5.02/5.27          | (r1_ordinal1 @ X61 @ X62)
% 5.02/5.27          | (r1_ordinal1 @ X62 @ X61))),
% 5.02/5.27      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 5.02/5.27  thf(redefinition_r1_ordinal1, axiom,
% 5.02/5.27    (![A:$i,B:$i]:
% 5.02/5.27     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 5.02/5.27       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 5.02/5.27  thf('3', plain,
% 5.02/5.27      (![X64 : $i, X65 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X64)
% 5.02/5.27          | ~ (v3_ordinal1 @ X65)
% 5.02/5.27          | (r1_tarski @ X64 @ X65)
% 5.02/5.27          | ~ (r1_ordinal1 @ X64 @ X65))),
% 5.02/5.27      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 5.02/5.27  thf('4', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i]:
% 5.02/5.27         ((r1_ordinal1 @ X0 @ X1)
% 5.02/5.27          | ~ (v3_ordinal1 @ X0)
% 5.02/5.27          | ~ (v3_ordinal1 @ X1)
% 5.02/5.27          | (r1_tarski @ X1 @ X0)
% 5.02/5.27          | ~ (v3_ordinal1 @ X0)
% 5.02/5.27          | ~ (v3_ordinal1 @ X1))),
% 5.02/5.27      inference('sup-', [status(thm)], ['2', '3'])).
% 5.02/5.27  thf('5', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i]:
% 5.02/5.27         ((r1_tarski @ X1 @ X0)
% 5.02/5.27          | ~ (v3_ordinal1 @ X1)
% 5.02/5.27          | ~ (v3_ordinal1 @ X0)
% 5.02/5.27          | (r1_ordinal1 @ X0 @ X1))),
% 5.02/5.27      inference('simplify', [status(thm)], ['4'])).
% 5.02/5.27  thf('6', plain,
% 5.02/5.27      (![X64 : $i, X65 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X64)
% 5.02/5.27          | ~ (v3_ordinal1 @ X65)
% 5.02/5.27          | (r1_tarski @ X64 @ X65)
% 5.02/5.27          | ~ (r1_ordinal1 @ X64 @ X65))),
% 5.02/5.27      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 5.02/5.27  thf('7', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X1)
% 5.02/5.27          | ~ (v3_ordinal1 @ X0)
% 5.02/5.27          | (r1_tarski @ X0 @ X1)
% 5.02/5.27          | (r1_tarski @ X1 @ X0)
% 5.02/5.27          | ~ (v3_ordinal1 @ X0)
% 5.02/5.27          | ~ (v3_ordinal1 @ X1))),
% 5.02/5.27      inference('sup-', [status(thm)], ['5', '6'])).
% 5.02/5.27  thf('8', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i]:
% 5.02/5.27         ((r1_tarski @ X1 @ X0)
% 5.02/5.27          | (r1_tarski @ X0 @ X1)
% 5.02/5.27          | ~ (v3_ordinal1 @ X0)
% 5.02/5.27          | ~ (v3_ordinal1 @ X1))),
% 5.02/5.27      inference('simplify', [status(thm)], ['7'])).
% 5.02/5.27  thf(t69_enumset1, axiom,
% 5.02/5.27    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 5.02/5.27  thf('9', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 5.02/5.27      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.02/5.27  thf('10', plain,
% 5.02/5.27      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.27  thf('11', plain,
% 5.02/5.27      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.02/5.27      inference('split', [status(esa)], ['10'])).
% 5.02/5.27  thf(d3_xboole_0, axiom,
% 5.02/5.27    (![A:$i,B:$i,C:$i]:
% 5.02/5.27     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 5.02/5.27       ( ![D:$i]:
% 5.02/5.27         ( ( r2_hidden @ D @ C ) <=>
% 5.02/5.27           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 5.02/5.27  thf('12', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.02/5.27         (~ (r2_hidden @ X0 @ X1)
% 5.02/5.27          | (r2_hidden @ X0 @ X2)
% 5.02/5.27          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 5.02/5.27      inference('cnf', [status(esa)], [d3_xboole_0])).
% 5.02/5.27  thf('13', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i, X3 : $i]:
% 5.02/5.27         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 5.02/5.27      inference('simplify', [status(thm)], ['12'])).
% 5.02/5.27  thf(l51_zfmisc_1, axiom,
% 5.02/5.27    (![A:$i,B:$i]:
% 5.02/5.27     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 5.02/5.27  thf('14', plain,
% 5.02/5.27      (![X37 : $i, X38 : $i]:
% 5.02/5.27         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 5.02/5.27      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 5.02/5.27  thf('15', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i, X3 : $i]:
% 5.02/5.27         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 5.02/5.27          | ~ (r2_hidden @ X0 @ X1))),
% 5.02/5.27      inference('demod', [status(thm)], ['13', '14'])).
% 5.02/5.27  thf('16', plain,
% 5.02/5.27      ((![X0 : $i]: (r2_hidden @ sk_A @ (k3_tarski @ (k2_tarski @ X0 @ sk_B))))
% 5.02/5.27         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.02/5.27      inference('sup-', [status(thm)], ['11', '15'])).
% 5.02/5.27  thf(t7_ordinal1, axiom,
% 5.02/5.27    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.02/5.27  thf('17', plain,
% 5.02/5.27      (![X71 : $i, X72 : $i]:
% 5.02/5.27         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 5.02/5.27      inference('cnf', [status(esa)], [t7_ordinal1])).
% 5.02/5.27  thf('18', plain,
% 5.02/5.27      ((![X0 : $i]:
% 5.02/5.27          ~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ sk_B)) @ sk_A))
% 5.02/5.27         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.02/5.27      inference('sup-', [status(thm)], ['16', '17'])).
% 5.02/5.27  thf('19', plain,
% 5.02/5.27      ((~ (r1_tarski @ (k3_tarski @ (k1_tarski @ sk_B)) @ sk_A))
% 5.02/5.27         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.02/5.27      inference('sup-', [status(thm)], ['9', '18'])).
% 5.02/5.27  thf('20', plain,
% 5.02/5.27      (((~ (v3_ordinal1 @ (k3_tarski @ (k1_tarski @ sk_B)))
% 5.02/5.27         | ~ (v3_ordinal1 @ sk_A)
% 5.02/5.27         | (r1_tarski @ sk_A @ (k3_tarski @ (k1_tarski @ sk_B)))))
% 5.02/5.27         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.02/5.27      inference('sup-', [status(thm)], ['8', '19'])).
% 5.02/5.27  thf('21', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 5.02/5.27      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.02/5.27  thf('22', plain,
% 5.02/5.27      (![X1 : $i, X3 : $i, X5 : $i]:
% 5.02/5.27         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 5.02/5.27          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 5.02/5.27          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 5.02/5.27          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 5.02/5.27      inference('cnf', [status(esa)], [d3_xboole_0])).
% 5.02/5.27  thf('23', plain,
% 5.02/5.27      (![X37 : $i, X38 : $i]:
% 5.02/5.27         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 5.02/5.27      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 5.02/5.27  thf('24', plain,
% 5.02/5.27      (![X1 : $i, X3 : $i, X5 : $i]:
% 5.02/5.27         (((X5) = (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 5.02/5.27          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 5.02/5.27          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 5.02/5.27          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 5.02/5.27      inference('demod', [status(thm)], ['22', '23'])).
% 5.02/5.27  thf('25', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i]:
% 5.02/5.27         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 5.02/5.27          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X0)
% 5.02/5.27          | ((X1) = (k3_tarski @ (k2_tarski @ X0 @ X0))))),
% 5.02/5.27      inference('eq_fact', [status(thm)], ['24'])).
% 5.02/5.27  thf('26', plain,
% 5.02/5.27      (![X0 : $i]:
% 5.02/5.27         (((X0) = (k3_tarski @ (k2_tarski @ X0 @ X0)))
% 5.02/5.27          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 5.02/5.27      inference('eq_fact', [status(thm)], ['25'])).
% 5.02/5.27  thf('27', plain,
% 5.02/5.27      (![X1 : $i, X3 : $i, X5 : $i]:
% 5.02/5.27         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 5.02/5.27          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 5.02/5.27          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 5.02/5.27      inference('cnf', [status(esa)], [d3_xboole_0])).
% 5.02/5.27  thf('28', plain,
% 5.02/5.27      (![X37 : $i, X38 : $i]:
% 5.02/5.27         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 5.02/5.27      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 5.02/5.27  thf('29', plain,
% 5.02/5.27      (![X1 : $i, X3 : $i, X5 : $i]:
% 5.02/5.27         (((X5) = (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 5.02/5.27          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 5.02/5.27          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 5.02/5.27      inference('demod', [status(thm)], ['27', '28'])).
% 5.02/5.27  thf('30', plain,
% 5.02/5.27      (![X0 : $i]:
% 5.02/5.27         (((X0) = (k3_tarski @ (k2_tarski @ X0 @ X0)))
% 5.02/5.27          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 5.02/5.27          | ((X0) = (k3_tarski @ (k2_tarski @ X0 @ X0))))),
% 5.02/5.27      inference('sup-', [status(thm)], ['26', '29'])).
% 5.02/5.27  thf('31', plain,
% 5.02/5.27      (![X0 : $i]:
% 5.02/5.27         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 5.02/5.27          | ((X0) = (k3_tarski @ (k2_tarski @ X0 @ X0))))),
% 5.02/5.27      inference('simplify', [status(thm)], ['30'])).
% 5.02/5.27  thf('32', plain,
% 5.02/5.27      (![X0 : $i]:
% 5.02/5.27         (((X0) = (k3_tarski @ (k2_tarski @ X0 @ X0)))
% 5.02/5.27          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 5.02/5.27      inference('eq_fact', [status(thm)], ['25'])).
% 5.02/5.27  thf('33', plain, (![X0 : $i]: ((X0) = (k3_tarski @ (k2_tarski @ X0 @ X0)))),
% 5.02/5.27      inference('clc', [status(thm)], ['31', '32'])).
% 5.02/5.27  thf('34', plain, (![X0 : $i]: ((X0) = (k3_tarski @ (k1_tarski @ X0)))),
% 5.02/5.27      inference('sup+', [status(thm)], ['21', '33'])).
% 5.02/5.27  thf('35', plain, ((v3_ordinal1 @ sk_B)),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.27  thf('36', plain, ((v3_ordinal1 @ sk_A)),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.27  thf('37', plain, (![X0 : $i]: ((X0) = (k3_tarski @ (k1_tarski @ X0)))),
% 5.02/5.27      inference('sup+', [status(thm)], ['21', '33'])).
% 5.02/5.27  thf('38', plain,
% 5.02/5.27      (((r1_tarski @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.02/5.27      inference('demod', [status(thm)], ['20', '34', '35', '36', '37'])).
% 5.02/5.27  thf('39', plain,
% 5.02/5.27      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.02/5.27      inference('split', [status(esa)], ['10'])).
% 5.02/5.27  thf(l1_zfmisc_1, axiom,
% 5.02/5.27    (![A:$i,B:$i]:
% 5.02/5.27     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 5.02/5.27  thf('40', plain,
% 5.02/5.27      (![X34 : $i, X36 : $i]:
% 5.02/5.27         ((r1_tarski @ (k1_tarski @ X34) @ X36) | ~ (r2_hidden @ X34 @ X36))),
% 5.02/5.27      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 5.02/5.27  thf('41', plain,
% 5.02/5.27      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 5.02/5.27         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.02/5.27      inference('sup-', [status(thm)], ['39', '40'])).
% 5.02/5.27  thf(t29_ordinal1, axiom,
% 5.02/5.27    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 5.02/5.27  thf('42', plain,
% 5.02/5.27      (![X70 : $i]:
% 5.02/5.27         ((v3_ordinal1 @ (k1_ordinal1 @ X70)) | ~ (v3_ordinal1 @ X70))),
% 5.02/5.27      inference('cnf', [status(esa)], [t29_ordinal1])).
% 5.02/5.27  thf(t26_ordinal1, axiom,
% 5.02/5.27    (![A:$i]:
% 5.02/5.27     ( ( v3_ordinal1 @ A ) =>
% 5.02/5.27       ( ![B:$i]:
% 5.02/5.27         ( ( v3_ordinal1 @ B ) =>
% 5.02/5.27           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 5.02/5.27  thf('43', plain,
% 5.02/5.27      (![X68 : $i, X69 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X68)
% 5.02/5.27          | (r1_ordinal1 @ X69 @ X68)
% 5.02/5.27          | (r2_hidden @ X68 @ X69)
% 5.02/5.27          | ~ (v3_ordinal1 @ X69))),
% 5.02/5.27      inference('cnf', [status(esa)], [t26_ordinal1])).
% 5.02/5.27  thf(d1_ordinal1, axiom,
% 5.02/5.27    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 5.02/5.27  thf('44', plain,
% 5.02/5.27      (![X63 : $i]:
% 5.02/5.27         ((k1_ordinal1 @ X63) = (k2_xboole_0 @ X63 @ (k1_tarski @ X63)))),
% 5.02/5.27      inference('cnf', [status(esa)], [d1_ordinal1])).
% 5.02/5.27  thf('45', plain,
% 5.02/5.27      (![X37 : $i, X38 : $i]:
% 5.02/5.27         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 5.02/5.27      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 5.02/5.27  thf('46', plain,
% 5.02/5.27      (![X63 : $i]:
% 5.02/5.27         ((k1_ordinal1 @ X63)
% 5.02/5.27           = (k3_tarski @ (k2_tarski @ X63 @ (k1_tarski @ X63))))),
% 5.02/5.27      inference('demod', [status(thm)], ['44', '45'])).
% 5.02/5.27  thf('47', plain,
% 5.02/5.27      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.02/5.27         (~ (r2_hidden @ X4 @ X2)
% 5.02/5.27          | (r2_hidden @ X4 @ X3)
% 5.02/5.27          | (r2_hidden @ X4 @ X1)
% 5.02/5.27          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 5.02/5.27      inference('cnf', [status(esa)], [d3_xboole_0])).
% 5.02/5.27  thf('48', plain,
% 5.02/5.27      (![X1 : $i, X3 : $i, X4 : $i]:
% 5.02/5.27         ((r2_hidden @ X4 @ X1)
% 5.02/5.27          | (r2_hidden @ X4 @ X3)
% 5.02/5.27          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 5.02/5.27      inference('simplify', [status(thm)], ['47'])).
% 5.02/5.27  thf('49', plain,
% 5.02/5.27      (![X37 : $i, X38 : $i]:
% 5.02/5.27         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 5.02/5.27      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 5.02/5.27  thf('50', plain,
% 5.02/5.27      (![X1 : $i, X3 : $i, X4 : $i]:
% 5.02/5.27         ((r2_hidden @ X4 @ X1)
% 5.02/5.27          | (r2_hidden @ X4 @ X3)
% 5.02/5.27          | ~ (r2_hidden @ X4 @ (k3_tarski @ (k2_tarski @ X3 @ X1))))),
% 5.02/5.27      inference('demod', [status(thm)], ['48', '49'])).
% 5.02/5.27  thf('51', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i]:
% 5.02/5.27         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 5.02/5.27          | (r2_hidden @ X1 @ X0)
% 5.02/5.27          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 5.02/5.27      inference('sup-', [status(thm)], ['46', '50'])).
% 5.02/5.27  thf('52', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 5.02/5.27          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 5.02/5.27          | ~ (v3_ordinal1 @ X1)
% 5.02/5.27          | (r2_hidden @ X1 @ (k1_tarski @ X0))
% 5.02/5.27          | (r2_hidden @ X1 @ X0))),
% 5.02/5.27      inference('sup-', [status(thm)], ['43', '51'])).
% 5.02/5.27  thf('53', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X0)
% 5.02/5.27          | (r2_hidden @ X1 @ X0)
% 5.02/5.27          | (r2_hidden @ X1 @ (k1_tarski @ X0))
% 5.02/5.27          | ~ (v3_ordinal1 @ X1)
% 5.02/5.27          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1))),
% 5.02/5.27      inference('sup-', [status(thm)], ['42', '52'])).
% 5.02/5.27  thf('54', plain,
% 5.02/5.27      (![X71 : $i, X72 : $i]:
% 5.02/5.27         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 5.02/5.27      inference('cnf', [status(esa)], [t7_ordinal1])).
% 5.02/5.27  thf('55', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i]:
% 5.02/5.27         ((r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 5.02/5.27          | ~ (v3_ordinal1 @ X1)
% 5.02/5.27          | (r2_hidden @ X1 @ X0)
% 5.02/5.27          | ~ (v3_ordinal1 @ X0)
% 5.02/5.27          | ~ (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 5.02/5.27      inference('sup-', [status(thm)], ['53', '54'])).
% 5.02/5.27  thf('56', plain,
% 5.02/5.27      (((~ (v3_ordinal1 @ sk_A)
% 5.02/5.27         | (r2_hidden @ sk_B @ sk_A)
% 5.02/5.27         | ~ (v3_ordinal1 @ sk_B)
% 5.02/5.27         | (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 5.02/5.27         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.02/5.27      inference('sup-', [status(thm)], ['41', '55'])).
% 5.02/5.27  thf('57', plain, ((v3_ordinal1 @ sk_A)),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.27  thf('58', plain, ((v3_ordinal1 @ sk_B)),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.27  thf('59', plain,
% 5.02/5.27      ((((r2_hidden @ sk_B @ sk_A)
% 5.02/5.27         | (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 5.02/5.27         <= (((r2_hidden @ sk_A @ sk_B)))),
% 5.02/5.27      inference('demod', [status(thm)], ['56', '57', '58'])).
% 5.02/5.27  thf('60', plain,
% 5.02/5.27      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 5.02/5.27         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.02/5.27      inference('split', [status(esa)], ['0'])).
% 5.02/5.27  thf('61', plain,
% 5.02/5.27      (((r2_hidden @ sk_B @ sk_A))
% 5.02/5.27         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) & 
% 5.02/5.27             ((r2_hidden @ sk_A @ sk_B)))),
% 5.02/5.27      inference('sup-', [status(thm)], ['59', '60'])).
% 5.02/5.27  thf('62', plain,
% 5.02/5.27      (![X71 : $i, X72 : $i]:
% 5.02/5.27         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 5.02/5.27      inference('cnf', [status(esa)], [t7_ordinal1])).
% 5.02/5.27  thf('63', plain,
% 5.02/5.27      ((~ (r1_tarski @ sk_A @ sk_B))
% 5.02/5.27         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) & 
% 5.02/5.27             ((r2_hidden @ sk_A @ sk_B)))),
% 5.02/5.27      inference('sup-', [status(thm)], ['61', '62'])).
% 5.02/5.27  thf('64', plain,
% 5.02/5.27      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 5.02/5.27       ~ ((r2_hidden @ sk_A @ sk_B))),
% 5.02/5.27      inference('sup-', [status(thm)], ['38', '63'])).
% 5.02/5.27  thf('65', plain,
% 5.02/5.27      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 5.02/5.27       ((r2_hidden @ sk_A @ sk_B))),
% 5.02/5.27      inference('split', [status(esa)], ['10'])).
% 5.02/5.27  thf('66', plain,
% 5.02/5.27      (![X70 : $i]:
% 5.02/5.27         ((v3_ordinal1 @ (k1_ordinal1 @ X70)) | ~ (v3_ordinal1 @ X70))),
% 5.02/5.27      inference('cnf', [status(esa)], [t29_ordinal1])).
% 5.02/5.27  thf('67', plain,
% 5.02/5.27      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 5.02/5.27         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.02/5.27      inference('split', [status(esa)], ['10'])).
% 5.02/5.27  thf('68', plain,
% 5.02/5.27      (![X64 : $i, X65 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X64)
% 5.02/5.27          | ~ (v3_ordinal1 @ X65)
% 5.02/5.27          | (r1_tarski @ X64 @ X65)
% 5.02/5.27          | ~ (r1_ordinal1 @ X64 @ X65))),
% 5.02/5.27      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 5.02/5.27  thf('69', plain,
% 5.02/5.27      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 5.02/5.27         | ~ (v3_ordinal1 @ sk_B)
% 5.02/5.27         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 5.02/5.27         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.02/5.27      inference('sup-', [status(thm)], ['67', '68'])).
% 5.02/5.27  thf('70', plain, ((v3_ordinal1 @ sk_B)),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.27  thf('71', plain,
% 5.02/5.27      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 5.02/5.27         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 5.02/5.27         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.02/5.27      inference('demod', [status(thm)], ['69', '70'])).
% 5.02/5.27  thf('72', plain,
% 5.02/5.27      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 5.02/5.27         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.02/5.27      inference('sup-', [status(thm)], ['66', '71'])).
% 5.02/5.27  thf('73', plain, ((v3_ordinal1 @ sk_A)),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.27  thf('74', plain,
% 5.02/5.27      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 5.02/5.27         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.02/5.27      inference('demod', [status(thm)], ['72', '73'])).
% 5.02/5.27  thf('75', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 5.02/5.27      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.02/5.27  thf('76', plain,
% 5.02/5.27      (![X63 : $i]:
% 5.02/5.27         ((k1_ordinal1 @ X63)
% 5.02/5.27           = (k3_tarski @ (k2_tarski @ X63 @ (k1_tarski @ X63))))),
% 5.02/5.27      inference('demod', [status(thm)], ['44', '45'])).
% 5.02/5.27  thf('77', plain,
% 5.02/5.27      (![X0 : $i]:
% 5.02/5.27         ((k1_ordinal1 @ X0)
% 5.02/5.27           = (k3_tarski @ (k2_tarski @ X0 @ (k2_tarski @ X0 @ X0))))),
% 5.02/5.27      inference('sup+', [status(thm)], ['75', '76'])).
% 5.02/5.27  thf('78', plain,
% 5.02/5.27      (![X68 : $i, X69 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X68)
% 5.02/5.27          | (r1_ordinal1 @ X69 @ X68)
% 5.02/5.27          | (r2_hidden @ X68 @ X69)
% 5.02/5.27          | ~ (v3_ordinal1 @ X69))),
% 5.02/5.27      inference('cnf', [status(esa)], [t26_ordinal1])).
% 5.02/5.27  thf('79', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.02/5.27         (~ (r2_hidden @ X0 @ X3)
% 5.02/5.27          | (r2_hidden @ X0 @ X2)
% 5.02/5.27          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 5.02/5.27      inference('cnf', [status(esa)], [d3_xboole_0])).
% 5.02/5.27  thf('80', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i, X3 : $i]:
% 5.02/5.27         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 5.02/5.27      inference('simplify', [status(thm)], ['79'])).
% 5.02/5.27  thf('81', plain,
% 5.02/5.27      (![X37 : $i, X38 : $i]:
% 5.02/5.27         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 5.02/5.27      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 5.02/5.27  thf('82', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i, X3 : $i]:
% 5.02/5.27         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 5.02/5.27          | ~ (r2_hidden @ X0 @ X3))),
% 5.02/5.27      inference('demod', [status(thm)], ['80', '81'])).
% 5.02/5.27  thf('83', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X0)
% 5.02/5.27          | (r1_ordinal1 @ X0 @ X1)
% 5.02/5.27          | ~ (v3_ordinal1 @ X1)
% 5.02/5.27          | (r2_hidden @ X1 @ (k3_tarski @ (k2_tarski @ X0 @ X2))))),
% 5.02/5.27      inference('sup-', [status(thm)], ['78', '82'])).
% 5.02/5.27  thf('84', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i]:
% 5.02/5.27         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 5.02/5.27          | ~ (v3_ordinal1 @ X1)
% 5.02/5.27          | (r1_ordinal1 @ X0 @ X1)
% 5.02/5.27          | ~ (v3_ordinal1 @ X0))),
% 5.02/5.27      inference('sup+', [status(thm)], ['77', '83'])).
% 5.02/5.27  thf('85', plain,
% 5.02/5.27      (![X71 : $i, X72 : $i]:
% 5.02/5.27         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 5.02/5.27      inference('cnf', [status(esa)], [t7_ordinal1])).
% 5.02/5.27  thf('86', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X0)
% 5.02/5.27          | (r1_ordinal1 @ X0 @ X1)
% 5.02/5.27          | ~ (v3_ordinal1 @ X1)
% 5.02/5.27          | ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X1))),
% 5.02/5.27      inference('sup-', [status(thm)], ['84', '85'])).
% 5.02/5.27  thf('87', plain,
% 5.02/5.27      (((~ (v3_ordinal1 @ sk_B)
% 5.02/5.27         | (r1_ordinal1 @ sk_A @ sk_B)
% 5.02/5.27         | ~ (v3_ordinal1 @ sk_A)))
% 5.02/5.27         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.02/5.27      inference('sup-', [status(thm)], ['74', '86'])).
% 5.02/5.27  thf('88', plain, ((v3_ordinal1 @ sk_B)),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.27  thf('89', plain, ((v3_ordinal1 @ sk_A)),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.27  thf('90', plain,
% 5.02/5.27      (((r1_ordinal1 @ sk_A @ sk_B))
% 5.02/5.27         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.02/5.27      inference('demod', [status(thm)], ['87', '88', '89'])).
% 5.02/5.27  thf('91', plain,
% 5.02/5.27      (![X64 : $i, X65 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X64)
% 5.02/5.27          | ~ (v3_ordinal1 @ X65)
% 5.02/5.27          | (r1_tarski @ X64 @ X65)
% 5.02/5.27          | ~ (r1_ordinal1 @ X64 @ X65))),
% 5.02/5.27      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 5.02/5.27  thf('92', plain,
% 5.02/5.27      ((((r1_tarski @ sk_A @ sk_B)
% 5.02/5.27         | ~ (v3_ordinal1 @ sk_B)
% 5.02/5.27         | ~ (v3_ordinal1 @ sk_A)))
% 5.02/5.27         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.02/5.27      inference('sup-', [status(thm)], ['90', '91'])).
% 5.02/5.27  thf('93', plain, ((v3_ordinal1 @ sk_B)),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.27  thf('94', plain, ((v3_ordinal1 @ sk_A)),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.27  thf('95', plain,
% 5.02/5.27      (((r1_tarski @ sk_A @ sk_B))
% 5.02/5.27         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.02/5.27      inference('demod', [status(thm)], ['92', '93', '94'])).
% 5.02/5.27  thf(t24_ordinal1, axiom,
% 5.02/5.27    (![A:$i]:
% 5.02/5.27     ( ( v3_ordinal1 @ A ) =>
% 5.02/5.27       ( ![B:$i]:
% 5.02/5.27         ( ( v3_ordinal1 @ B ) =>
% 5.02/5.27           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 5.02/5.27                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 5.02/5.27  thf('96', plain,
% 5.02/5.27      (![X66 : $i, X67 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X66)
% 5.02/5.27          | (r2_hidden @ X67 @ X66)
% 5.02/5.27          | ((X67) = (X66))
% 5.02/5.27          | (r2_hidden @ X66 @ X67)
% 5.02/5.27          | ~ (v3_ordinal1 @ X67))),
% 5.02/5.27      inference('cnf', [status(esa)], [t24_ordinal1])).
% 5.02/5.27  thf('97', plain,
% 5.02/5.27      (![X71 : $i, X72 : $i]:
% 5.02/5.27         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 5.02/5.27      inference('cnf', [status(esa)], [t7_ordinal1])).
% 5.02/5.27  thf('98', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X1)
% 5.02/5.27          | (r2_hidden @ X0 @ X1)
% 5.02/5.27          | ((X1) = (X0))
% 5.02/5.27          | ~ (v3_ordinal1 @ X0)
% 5.02/5.27          | ~ (r1_tarski @ X0 @ X1))),
% 5.02/5.27      inference('sup-', [status(thm)], ['96', '97'])).
% 5.02/5.27  thf('99', plain,
% 5.02/5.27      (((~ (v3_ordinal1 @ sk_A)
% 5.02/5.27         | ((sk_B) = (sk_A))
% 5.02/5.27         | (r2_hidden @ sk_A @ sk_B)
% 5.02/5.27         | ~ (v3_ordinal1 @ sk_B)))
% 5.02/5.27         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.02/5.27      inference('sup-', [status(thm)], ['95', '98'])).
% 5.02/5.27  thf('100', plain, ((v3_ordinal1 @ sk_A)),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.27  thf('101', plain, ((v3_ordinal1 @ sk_B)),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.27  thf('102', plain,
% 5.02/5.27      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B)))
% 5.02/5.27         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.02/5.27      inference('demod', [status(thm)], ['99', '100', '101'])).
% 5.02/5.27  thf('103', plain,
% 5.02/5.27      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 5.02/5.27      inference('split', [status(esa)], ['0'])).
% 5.02/5.27  thf('104', plain,
% 5.02/5.27      ((((sk_B) = (sk_A)))
% 5.02/5.27         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 5.02/5.27             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.02/5.27      inference('sup-', [status(thm)], ['102', '103'])).
% 5.02/5.27  thf('105', plain,
% 5.02/5.27      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 5.02/5.27         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.02/5.27      inference('demod', [status(thm)], ['72', '73'])).
% 5.02/5.27  thf('106', plain,
% 5.02/5.27      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A))
% 5.02/5.27         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 5.02/5.27             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.02/5.27      inference('sup+', [status(thm)], ['104', '105'])).
% 5.02/5.27  thf('107', plain,
% 5.02/5.27      (![X70 : $i]:
% 5.02/5.27         ((v3_ordinal1 @ (k1_ordinal1 @ X70)) | ~ (v3_ordinal1 @ X70))),
% 5.02/5.27      inference('cnf', [status(esa)], [t29_ordinal1])).
% 5.02/5.27  thf('108', plain,
% 5.02/5.27      (![X61 : $i, X62 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X61)
% 5.02/5.27          | ~ (v3_ordinal1 @ X62)
% 5.02/5.27          | (r1_ordinal1 @ X61 @ X62)
% 5.02/5.27          | (r1_ordinal1 @ X62 @ X61))),
% 5.02/5.27      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 5.02/5.27  thf('109', plain,
% 5.02/5.27      (![X0 : $i]:
% 5.02/5.27         ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 5.02/5.27      inference('eq_fact', [status(thm)], ['108'])).
% 5.02/5.27  thf('110', plain,
% 5.02/5.27      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0))),
% 5.02/5.27      inference('simplify', [status(thm)], ['109'])).
% 5.02/5.27  thf('111', plain,
% 5.02/5.27      (![X64 : $i, X65 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X64)
% 5.02/5.27          | ~ (v3_ordinal1 @ X65)
% 5.02/5.27          | (r1_tarski @ X64 @ X65)
% 5.02/5.27          | ~ (r1_ordinal1 @ X64 @ X65))),
% 5.02/5.27      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 5.02/5.27  thf('112', plain,
% 5.02/5.27      (![X0 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X0)
% 5.02/5.27          | (r1_tarski @ X0 @ X0)
% 5.02/5.27          | ~ (v3_ordinal1 @ X0)
% 5.02/5.27          | ~ (v3_ordinal1 @ X0))),
% 5.02/5.27      inference('sup-', [status(thm)], ['110', '111'])).
% 5.02/5.27  thf('113', plain,
% 5.02/5.27      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 5.02/5.27      inference('simplify', [status(thm)], ['112'])).
% 5.02/5.27  thf('114', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X0)
% 5.02/5.27          | (r1_ordinal1 @ X0 @ X1)
% 5.02/5.27          | ~ (v3_ordinal1 @ X1)
% 5.02/5.27          | ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X1))),
% 5.02/5.27      inference('sup-', [status(thm)], ['84', '85'])).
% 5.02/5.27  thf('115', plain,
% 5.02/5.27      (![X0 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 5.02/5.27          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 5.02/5.27          | (r1_ordinal1 @ X0 @ (k1_ordinal1 @ X0))
% 5.02/5.27          | ~ (v3_ordinal1 @ X0))),
% 5.02/5.27      inference('sup-', [status(thm)], ['113', '114'])).
% 5.02/5.27  thf('116', plain,
% 5.02/5.27      (![X0 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X0)
% 5.02/5.27          | (r1_ordinal1 @ X0 @ (k1_ordinal1 @ X0))
% 5.02/5.27          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0)))),
% 5.02/5.27      inference('simplify', [status(thm)], ['115'])).
% 5.02/5.27  thf('117', plain,
% 5.02/5.27      (![X70 : $i]:
% 5.02/5.27         ((v3_ordinal1 @ (k1_ordinal1 @ X70)) | ~ (v3_ordinal1 @ X70))),
% 5.02/5.27      inference('cnf', [status(esa)], [t29_ordinal1])).
% 5.02/5.27  thf('118', plain,
% 5.02/5.27      (![X0 : $i]:
% 5.02/5.27         ((r1_ordinal1 @ X0 @ (k1_ordinal1 @ X0)) | ~ (v3_ordinal1 @ X0))),
% 5.02/5.27      inference('clc', [status(thm)], ['116', '117'])).
% 5.02/5.27  thf('119', plain,
% 5.02/5.27      (![X64 : $i, X65 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X64)
% 5.02/5.27          | ~ (v3_ordinal1 @ X65)
% 5.02/5.27          | (r1_tarski @ X64 @ X65)
% 5.02/5.27          | ~ (r1_ordinal1 @ X64 @ X65))),
% 5.02/5.27      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 5.02/5.27  thf('120', plain,
% 5.02/5.27      (![X0 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X0)
% 5.02/5.27          | (r1_tarski @ X0 @ (k1_ordinal1 @ X0))
% 5.02/5.27          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 5.02/5.27          | ~ (v3_ordinal1 @ X0))),
% 5.02/5.27      inference('sup-', [status(thm)], ['118', '119'])).
% 5.02/5.27  thf('121', plain,
% 5.02/5.27      (![X0 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 5.02/5.27          | (r1_tarski @ X0 @ (k1_ordinal1 @ X0))
% 5.02/5.27          | ~ (v3_ordinal1 @ X0))),
% 5.02/5.27      inference('simplify', [status(thm)], ['120'])).
% 5.02/5.27  thf('122', plain,
% 5.02/5.27      (![X70 : $i]:
% 5.02/5.27         ((v3_ordinal1 @ (k1_ordinal1 @ X70)) | ~ (v3_ordinal1 @ X70))),
% 5.02/5.27      inference('cnf', [status(esa)], [t29_ordinal1])).
% 5.02/5.27  thf('123', plain,
% 5.02/5.27      (![X0 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X0) | (r1_tarski @ X0 @ (k1_ordinal1 @ X0)))),
% 5.02/5.27      inference('clc', [status(thm)], ['121', '122'])).
% 5.02/5.27  thf('124', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X1)
% 5.02/5.27          | (r2_hidden @ X0 @ X1)
% 5.02/5.27          | ((X1) = (X0))
% 5.02/5.27          | ~ (v3_ordinal1 @ X0)
% 5.02/5.27          | ~ (r1_tarski @ X0 @ X1))),
% 5.02/5.27      inference('sup-', [status(thm)], ['96', '97'])).
% 5.02/5.27  thf('125', plain,
% 5.02/5.27      (![X0 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X0)
% 5.02/5.27          | ~ (v3_ordinal1 @ X0)
% 5.02/5.27          | ((k1_ordinal1 @ X0) = (X0))
% 5.02/5.27          | (r2_hidden @ X0 @ (k1_ordinal1 @ X0))
% 5.02/5.27          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0)))),
% 5.02/5.27      inference('sup-', [status(thm)], ['123', '124'])).
% 5.02/5.27  thf('126', plain,
% 5.02/5.27      (![X0 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 5.02/5.27          | (r2_hidden @ X0 @ (k1_ordinal1 @ X0))
% 5.02/5.27          | ((k1_ordinal1 @ X0) = (X0))
% 5.02/5.27          | ~ (v3_ordinal1 @ X0))),
% 5.02/5.27      inference('simplify', [status(thm)], ['125'])).
% 5.02/5.27  thf('127', plain,
% 5.02/5.27      (![X0 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X0)
% 5.02/5.27          | ~ (v3_ordinal1 @ X0)
% 5.02/5.27          | ((k1_ordinal1 @ X0) = (X0))
% 5.02/5.27          | (r2_hidden @ X0 @ (k1_ordinal1 @ X0)))),
% 5.02/5.27      inference('sup-', [status(thm)], ['107', '126'])).
% 5.02/5.27  thf('128', plain,
% 5.02/5.27      (![X0 : $i]:
% 5.02/5.27         ((r2_hidden @ X0 @ (k1_ordinal1 @ X0))
% 5.02/5.27          | ((k1_ordinal1 @ X0) = (X0))
% 5.02/5.27          | ~ (v3_ordinal1 @ X0))),
% 5.02/5.27      inference('simplify', [status(thm)], ['127'])).
% 5.02/5.27  thf('129', plain,
% 5.02/5.27      (![X71 : $i, X72 : $i]:
% 5.02/5.27         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 5.02/5.27      inference('cnf', [status(esa)], [t7_ordinal1])).
% 5.02/5.27  thf('130', plain,
% 5.02/5.27      (![X0 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X0)
% 5.02/5.27          | ((k1_ordinal1 @ X0) = (X0))
% 5.02/5.27          | ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0))),
% 5.02/5.27      inference('sup-', [status(thm)], ['128', '129'])).
% 5.02/5.27  thf('131', plain,
% 5.02/5.27      (((((k1_ordinal1 @ sk_A) = (sk_A)) | ~ (v3_ordinal1 @ sk_A)))
% 5.02/5.27         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 5.02/5.27             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.02/5.27      inference('sup-', [status(thm)], ['106', '130'])).
% 5.02/5.27  thf('132', plain, ((v3_ordinal1 @ sk_A)),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.27  thf('133', plain,
% 5.02/5.27      ((((k1_ordinal1 @ sk_A) = (sk_A)))
% 5.02/5.27         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 5.02/5.27             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.02/5.27      inference('demod', [status(thm)], ['131', '132'])).
% 5.02/5.27  thf('134', plain,
% 5.02/5.27      (![X63 : $i]:
% 5.02/5.27         ((k1_ordinal1 @ X63)
% 5.02/5.27           = (k3_tarski @ (k2_tarski @ X63 @ (k1_tarski @ X63))))),
% 5.02/5.27      inference('demod', [status(thm)], ['44', '45'])).
% 5.02/5.27  thf(t70_enumset1, axiom,
% 5.02/5.27    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 5.02/5.27  thf('135', plain,
% 5.02/5.27      (![X7 : $i, X8 : $i]:
% 5.02/5.27         ((k1_enumset1 @ X7 @ X7 @ X8) = (k2_tarski @ X7 @ X8))),
% 5.02/5.27      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.02/5.27  thf('136', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 5.02/5.27      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.02/5.27  thf('137', plain,
% 5.02/5.27      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 5.02/5.27      inference('sup+', [status(thm)], ['135', '136'])).
% 5.02/5.27  thf(t71_enumset1, axiom,
% 5.02/5.27    (![A:$i,B:$i,C:$i]:
% 5.02/5.27     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 5.02/5.27  thf('138', plain,
% 5.02/5.27      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.02/5.27         ((k2_enumset1 @ X9 @ X9 @ X10 @ X11) = (k1_enumset1 @ X9 @ X10 @ X11))),
% 5.02/5.27      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.02/5.27  thf(t72_enumset1, axiom,
% 5.02/5.27    (![A:$i,B:$i,C:$i,D:$i]:
% 5.02/5.27     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 5.02/5.27  thf('139', plain,
% 5.02/5.27      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.02/5.27         ((k3_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15)
% 5.02/5.27           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 5.02/5.27      inference('cnf', [status(esa)], [t72_enumset1])).
% 5.02/5.27  thf(t73_enumset1, axiom,
% 5.02/5.27    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 5.02/5.27     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 5.02/5.27       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 5.02/5.27  thf('140', plain,
% 5.02/5.27      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 5.02/5.27         ((k4_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20)
% 5.02/5.27           = (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 5.02/5.27      inference('cnf', [status(esa)], [t73_enumset1])).
% 5.02/5.27  thf(t74_enumset1, axiom,
% 5.02/5.27    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.02/5.27     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 5.02/5.27       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 5.02/5.27  thf('141', plain,
% 5.02/5.27      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 5.02/5.27         ((k5_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26)
% 5.02/5.27           = (k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26))),
% 5.02/5.27      inference('cnf', [status(esa)], [t74_enumset1])).
% 5.02/5.27  thf(t75_enumset1, axiom,
% 5.02/5.27    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 5.02/5.27     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 5.02/5.27       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 5.02/5.27  thf('142', plain,
% 5.02/5.27      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 5.02/5.27         ((k6_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33)
% 5.02/5.27           = (k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 5.02/5.27      inference('cnf', [status(esa)], [t75_enumset1])).
% 5.02/5.27  thf(d6_enumset1, axiom,
% 5.02/5.27    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 5.02/5.27     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 5.02/5.27       ( ![J:$i]:
% 5.02/5.27         ( ( r2_hidden @ J @ I ) <=>
% 5.02/5.27           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 5.02/5.27                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 5.02/5.27                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 5.02/5.27  thf(zf_stmt_1, type, zip_tseitin_0 :
% 5.02/5.27      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 5.02/5.27  thf(zf_stmt_2, axiom,
% 5.02/5.27    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 5.02/5.27     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 5.02/5.27       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 5.02/5.27         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 5.02/5.27         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 5.02/5.27  thf(zf_stmt_3, axiom,
% 5.02/5.27    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 5.02/5.27     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 5.02/5.27       ( ![J:$i]:
% 5.02/5.27         ( ( r2_hidden @ J @ I ) <=>
% 5.02/5.27           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 5.02/5.27  thf('143', plain,
% 5.02/5.27      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, 
% 5.02/5.27         X56 : $i, X57 : $i, X58 : $i]:
% 5.02/5.27         ((zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57)
% 5.02/5.27          | (r2_hidden @ X49 @ X58)
% 5.02/5.27          | ((X58)
% 5.02/5.27              != (k6_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50)))),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.02/5.27  thf('144', plain,
% 5.02/5.27      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, 
% 5.02/5.27         X56 : $i, X57 : $i]:
% 5.02/5.27         ((r2_hidden @ X49 @ 
% 5.02/5.27           (k6_enumset1 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 @ X51 @ X50))
% 5.02/5.27          | (zip_tseitin_0 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ 
% 5.02/5.27             X57))),
% 5.02/5.27      inference('simplify', [status(thm)], ['143'])).
% 5.02/5.27  thf('145', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 5.02/5.27         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 5.02/5.27          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 5.02/5.27      inference('sup+', [status(thm)], ['142', '144'])).
% 5.02/5.27  thf('146', plain,
% 5.02/5.27      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, 
% 5.02/5.27         X46 : $i, X47 : $i]:
% 5.02/5.27         (((X40) != (X39))
% 5.02/5.27          | ~ (zip_tseitin_0 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ 
% 5.02/5.27               X39))),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.02/5.27  thf('147', plain,
% 5.02/5.27      (![X39 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, 
% 5.02/5.27         X47 : $i]:
% 5.02/5.27         ~ (zip_tseitin_0 @ X39 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X39)),
% 5.02/5.27      inference('simplify', [status(thm)], ['146'])).
% 5.02/5.27  thf('148', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 5.02/5.27         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 5.02/5.27      inference('sup-', [status(thm)], ['145', '147'])).
% 5.02/5.27  thf('149', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 5.02/5.27         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 5.02/5.27      inference('sup+', [status(thm)], ['141', '148'])).
% 5.02/5.27  thf('150', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.02/5.27         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 5.02/5.27      inference('sup+', [status(thm)], ['140', '149'])).
% 5.02/5.27  thf('151', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.02/5.27         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 5.02/5.27      inference('sup+', [status(thm)], ['139', '150'])).
% 5.02/5.27  thf('152', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.02/5.27         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 5.02/5.27      inference('sup+', [status(thm)], ['138', '151'])).
% 5.02/5.27  thf('153', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 5.02/5.27      inference('sup+', [status(thm)], ['137', '152'])).
% 5.02/5.27  thf('154', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i, X3 : $i]:
% 5.02/5.27         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 5.02/5.27          | ~ (r2_hidden @ X0 @ X1))),
% 5.02/5.27      inference('demod', [status(thm)], ['13', '14'])).
% 5.02/5.27  thf('155', plain,
% 5.02/5.27      (![X0 : $i, X1 : $i]:
% 5.02/5.27         (r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ (k1_tarski @ X0))))),
% 5.02/5.27      inference('sup-', [status(thm)], ['153', '154'])).
% 5.02/5.27  thf('156', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 5.02/5.27      inference('sup+', [status(thm)], ['134', '155'])).
% 5.02/5.27  thf('157', plain,
% 5.02/5.27      (![X71 : $i, X72 : $i]:
% 5.02/5.27         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 5.02/5.27      inference('cnf', [status(esa)], [t7_ordinal1])).
% 5.02/5.27  thf('158', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 5.02/5.27      inference('sup-', [status(thm)], ['156', '157'])).
% 5.02/5.27  thf('159', plain,
% 5.02/5.27      ((~ (r1_tarski @ sk_A @ sk_A))
% 5.02/5.27         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 5.02/5.27             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 5.02/5.27      inference('sup-', [status(thm)], ['133', '158'])).
% 5.02/5.27  thf('160', plain, ((v3_ordinal1 @ sk_A)),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.27  thf('161', plain,
% 5.02/5.27      (![X61 : $i, X62 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X61)
% 5.02/5.27          | ~ (v3_ordinal1 @ X62)
% 5.02/5.27          | (r1_ordinal1 @ X61 @ X62)
% 5.02/5.27          | (r1_ordinal1 @ X62 @ X61))),
% 5.02/5.27      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 5.02/5.27  thf('162', plain,
% 5.02/5.27      (![X0 : $i]:
% 5.02/5.27         ((r1_ordinal1 @ X0 @ sk_A)
% 5.02/5.27          | (r1_ordinal1 @ sk_A @ X0)
% 5.02/5.27          | ~ (v3_ordinal1 @ X0))),
% 5.02/5.27      inference('sup-', [status(thm)], ['160', '161'])).
% 5.02/5.27  thf('163', plain, ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ sk_A))),
% 5.02/5.27      inference('eq_fact', [status(thm)], ['162'])).
% 5.02/5.27  thf('164', plain, ((v3_ordinal1 @ sk_A)),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.27  thf('165', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 5.02/5.27      inference('demod', [status(thm)], ['163', '164'])).
% 5.02/5.27  thf('166', plain,
% 5.02/5.27      (![X64 : $i, X65 : $i]:
% 5.02/5.27         (~ (v3_ordinal1 @ X64)
% 5.02/5.27          | ~ (v3_ordinal1 @ X65)
% 5.02/5.27          | (r1_tarski @ X64 @ X65)
% 5.02/5.27          | ~ (r1_ordinal1 @ X64 @ X65))),
% 5.02/5.27      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 5.02/5.27  thf('167', plain,
% 5.02/5.27      (((r1_tarski @ sk_A @ sk_A)
% 5.02/5.27        | ~ (v3_ordinal1 @ sk_A)
% 5.02/5.27        | ~ (v3_ordinal1 @ sk_A))),
% 5.02/5.27      inference('sup-', [status(thm)], ['165', '166'])).
% 5.02/5.27  thf('168', plain, ((v3_ordinal1 @ sk_A)),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.27  thf('169', plain, ((v3_ordinal1 @ sk_A)),
% 5.02/5.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.02/5.27  thf('170', plain, ((r1_tarski @ sk_A @ sk_A)),
% 5.02/5.27      inference('demod', [status(thm)], ['167', '168', '169'])).
% 5.02/5.27  thf('171', plain,
% 5.02/5.27      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 5.02/5.27       ((r2_hidden @ sk_A @ sk_B))),
% 5.02/5.27      inference('demod', [status(thm)], ['159', '170'])).
% 5.02/5.27  thf('172', plain, ($false),
% 5.02/5.27      inference('sat_resolution*', [status(thm)], ['1', '64', '65', '171'])).
% 5.02/5.27  
% 5.02/5.27  % SZS output end Refutation
% 5.02/5.27  
% 5.02/5.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
