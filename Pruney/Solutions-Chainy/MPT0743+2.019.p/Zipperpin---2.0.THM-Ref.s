%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JtN4JNov5M

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:55 EST 2020

% Result     : Theorem 4.78s
% Output     : Refutation 4.78s
% Verified   : 
% Statistics : Number of formulae       :  228 ( 927 expanded)
%              Number of leaves         :   41 ( 283 expanded)
%              Depth                    :   23
%              Number of atoms          : 1985 (8538 expanded)
%              Number of equality atoms :  104 ( 369 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('3',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('6',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('8',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k3_tarski @ ( k2_tarski @ X5 @ X3 ) ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_A @ ( k3_tarski @ ( k2_tarski @ X0 @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ ( k3_tarski @ ( k1_tarski @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('11',plain,(
    ! [X36: $i,X38: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X36 ) @ X38 )
      | ~ ( r2_hidden @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('12',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k3_tarski @ ( k1_tarski @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('13',plain,(
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

thf('14',plain,(
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

thf('15',plain,(
    ! [X63: $i] :
      ( ( k1_ordinal1 @ X63 )
      = ( k2_xboole_0 @ X63 @ ( k1_tarski @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('16',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('17',plain,(
    ! [X63: $i] :
      ( ( k1_ordinal1 @ X63 )
      = ( k3_tarski @ ( k2_tarski @ X63 @ ( k1_tarski @ X63 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('19',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('21',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k3_tarski @ ( k2_tarski @ X5 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('25',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r2_hidden @ ( k3_tarski @ ( k1_tarski @ sk_B ) ) @ sk_A )
      | ~ ( v3_ordinal1 @ ( k3_tarski @ ( k1_tarski @ sk_B ) ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ ( k3_tarski @ ( k1_tarski @ sk_B ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','26'])).

thf('28',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('31',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('32',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k3_tarski @ ( k2_tarski @ X5 @ X3 ) ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X0 )
      | ( X1
        = ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['33'])).

thf('35',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('36',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('37',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k3_tarski @ ( k2_tarski @ X5 @ X3 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['33'])).

thf('41',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','41'])).

thf('44',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','41'])).

thf('46',plain,
    ( ( ( r2_hidden @ sk_B @ sk_A )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['27','28','42','43','44','45'])).

thf('47',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['46','49'])).

thf('51',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('54',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( v3_ordinal1 @ X68 )
      | ( r1_ordinal1 @ X69 @ X68 )
      | ( r2_hidden @ X68 @ X69 )
      | ~ ( v3_ordinal1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('55',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( v3_ordinal1 @ X68 )
      | ( r1_ordinal1 @ X69 @ X68 )
      | ( r2_hidden @ X68 @ X69 )
      | ~ ( v3_ordinal1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('62',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v3_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X65 )
      | ( r1_tarski @ X64 @ X65 )
      | ~ ( r1_ordinal1 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('66',plain,(
    ! [X63: $i] :
      ( ( k1_ordinal1 @ X63 )
      = ( k3_tarski @ ( k2_tarski @ X63 @ ( k1_tarski @ X63 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k3_tarski @ ( k2_tarski @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( v3_ordinal1 @ X68 )
      | ( r1_ordinal1 @ X69 @ X68 )
      | ( r2_hidden @ X68 @ X69 )
      | ~ ( v3_ordinal1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('69',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('70',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('72',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k3_tarski @ ( k2_tarski @ X5 @ X3 ) ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k3_tarski @ ( k2_tarski @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['68','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','73'])).

thf('75',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X70: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X70 ) )
      | ~ ( v3_ordinal1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v3_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X65 )
      | ( r1_tarski @ X64 @ X65 )
      | ~ ( r1_ordinal1 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X70: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X70 ) )
      | ~ ( v3_ordinal1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k3_tarski @ ( k2_tarski @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('87',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( v3_ordinal1 @ X68 )
      | ( r1_ordinal1 @ X69 @ X68 )
      | ( r2_hidden @ X68 @ X69 )
      | ~ ( v3_ordinal1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('88',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('89',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v3_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X65 )
      | ( r1_tarski @ X64 @ X65 )
      | ~ ( r1_ordinal1 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('94',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('98',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( v3_ordinal1 @ X66 )
      | ( r2_hidden @ X67 @ X66 )
      | ( X67 = X66 )
      | ( r2_hidden @ X66 @ X67 )
      | ~ ( v3_ordinal1 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('99',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( sk_A = sk_B )
      | ( r2_hidden @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k3_tarski @ ( k2_tarski @ X5 @ X3 ) ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ( sk_A = sk_B )
        | ( r2_hidden @ sk_B @ ( k3_tarski @ ( k2_tarski @ sk_A @ X0 ) ) ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_A = sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['86','106'])).

thf('108',plain,(
    ! [X70: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X70 ) )
      | ~ ( v3_ordinal1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('109',plain,(
    ! [X70: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X70 ) )
      | ~ ( v3_ordinal1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('110',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('111',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v3_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X65 )
      | ( r1_tarski @ X64 @ X65 )
      | ~ ( r1_ordinal1 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('112',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['109','114'])).

thf('116',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('119',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['108','121'])).

thf('123',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('126',plain,
    ( ( ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( sk_A = sk_B )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['107','126'])).

thf('128',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_A = sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['86','106'])).

thf('129',plain,
    ( ( ( r2_hidden @ sk_B @ sk_B )
      | ( sk_A = sk_B )
      | ( sk_A = sk_B ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_B @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( ( ( sk_A = sk_B )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['107','126'])).

thf('132',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_A = sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['86','106'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('134',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ~ ( r2_hidden @ sk_B @ sk_B )
      | ( sk_A = sk_B )
      | ( sk_A = sk_B ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['131','134'])).

thf('136',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r2_hidden @ sk_B @ sk_B ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['130','136'])).

thf('138',plain,
    ( ( ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('139',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('140',plain,
    ( ( ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ~ ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( ~ ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['137','140'])).

thf('142',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['130','136'])).

thf('143',plain,
    ( ( ~ ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_A
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( sk_A
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','143'])).

thf('145',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X63: $i] :
      ( ( k1_ordinal1 @ X63 )
      = ( k3_tarski @ ( k2_tarski @ X63 @ ( k1_tarski @ X63 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('148',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X9 @ X9 @ X10 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('149',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('151',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X11 @ X11 @ X12 @ X13 )
      = ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('152',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k3_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('153',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('154',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k5_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('155',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k6_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 ) ) ),
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

thf('156',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( zip_tseitin_0 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 )
      | ( r2_hidden @ X51 @ X60 )
      | ( X60
       != ( k6_enumset1 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('157',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( r2_hidden @ X51 @ ( k6_enumset1 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52 ) )
      | ( zip_tseitin_0 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['155','157'])).

thf('159',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X42 != X41 )
      | ~ ( zip_tseitin_0 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('160',plain,(
    ! [X41: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ~ ( zip_tseitin_0 @ X41 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X41 ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['158','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['154','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['153','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['152','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['151','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['150','165'])).

thf('167',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k3_tarski @ ( k2_tarski @ X5 @ X3 ) ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['147','168'])).

thf('170',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ~ ( r1_tarski @ X72 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('171',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['146','171'])).

thf('173',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference(eq_fact,[status(thm)],['175'])).

thf('177',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    r1_ordinal1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v3_ordinal1 @ X64 )
      | ~ ( v3_ordinal1 @ X65 )
      | ( r1_tarski @ X64 @ X65 )
      | ~ ( r1_ordinal1 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('180',plain,
    ( ( r1_tarski @ sk_A @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    r1_tarski @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['180','181','182'])).

thf('184',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['172','183'])).

thf('185',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','52','53','184'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JtN4JNov5M
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:04:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 4.78/5.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.78/5.03  % Solved by: fo/fo7.sh
% 4.78/5.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.78/5.03  % done 7752 iterations in 4.560s
% 4.78/5.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.78/5.03  % SZS output start Refutation
% 4.78/5.03  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.78/5.03  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 4.78/5.03  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.78/5.03  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 4.78/5.03  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 4.78/5.03  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.78/5.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 4.78/5.03                                               $i > $i > $i > $o).
% 4.78/5.03  thf(sk_A_type, type, sk_A: $i).
% 4.78/5.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.78/5.03  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 4.78/5.03  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 4.78/5.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.78/5.03  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.78/5.03  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 4.78/5.03  thf(sk_B_type, type, sk_B: $i).
% 4.78/5.03  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 4.78/5.03  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 4.78/5.03                                           $i > $i).
% 4.78/5.03  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 4.78/5.03  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 4.78/5.03  thf(t33_ordinal1, conjecture,
% 4.78/5.03    (![A:$i]:
% 4.78/5.03     ( ( v3_ordinal1 @ A ) =>
% 4.78/5.03       ( ![B:$i]:
% 4.78/5.03         ( ( v3_ordinal1 @ B ) =>
% 4.78/5.03           ( ( r2_hidden @ A @ B ) <=>
% 4.78/5.03             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 4.78/5.03  thf(zf_stmt_0, negated_conjecture,
% 4.78/5.03    (~( ![A:$i]:
% 4.78/5.03        ( ( v3_ordinal1 @ A ) =>
% 4.78/5.03          ( ![B:$i]:
% 4.78/5.03            ( ( v3_ordinal1 @ B ) =>
% 4.78/5.03              ( ( r2_hidden @ A @ B ) <=>
% 4.78/5.03                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 4.78/5.03    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 4.78/5.03  thf('0', plain,
% 4.78/5.03      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 4.78/5.03        | ~ (r2_hidden @ sk_A @ sk_B))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('1', plain,
% 4.78/5.03      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 4.78/5.03       ~ ((r2_hidden @ sk_A @ sk_B))),
% 4.78/5.03      inference('split', [status(esa)], ['0'])).
% 4.78/5.03  thf(t69_enumset1, axiom,
% 4.78/5.03    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 4.78/5.03  thf('2', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 4.78/5.03      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.78/5.03  thf('3', plain,
% 4.78/5.03      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('4', plain,
% 4.78/5.03      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('split', [status(esa)], ['3'])).
% 4.78/5.03  thf(d3_xboole_0, axiom,
% 4.78/5.03    (![A:$i,B:$i,C:$i]:
% 4.78/5.03     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 4.78/5.03       ( ![D:$i]:
% 4.78/5.03         ( ( r2_hidden @ D @ C ) <=>
% 4.78/5.03           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 4.78/5.03  thf('5', plain,
% 4.78/5.03      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X2 @ X3)
% 4.78/5.03          | (r2_hidden @ X2 @ X4)
% 4.78/5.03          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 4.78/5.03      inference('cnf', [status(esa)], [d3_xboole_0])).
% 4.78/5.03  thf('6', plain,
% 4.78/5.03      (![X2 : $i, X3 : $i, X5 : $i]:
% 4.78/5.03         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 4.78/5.03      inference('simplify', [status(thm)], ['5'])).
% 4.78/5.03  thf(l51_zfmisc_1, axiom,
% 4.78/5.03    (![A:$i,B:$i]:
% 4.78/5.03     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.78/5.03  thf('7', plain,
% 4.78/5.03      (![X39 : $i, X40 : $i]:
% 4.78/5.03         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 4.78/5.03      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.78/5.03  thf('8', plain,
% 4.78/5.03      (![X2 : $i, X3 : $i, X5 : $i]:
% 4.78/5.03         ((r2_hidden @ X2 @ (k3_tarski @ (k2_tarski @ X5 @ X3)))
% 4.78/5.03          | ~ (r2_hidden @ X2 @ X3))),
% 4.78/5.03      inference('demod', [status(thm)], ['6', '7'])).
% 4.78/5.03  thf('9', plain,
% 4.78/5.03      ((![X0 : $i]: (r2_hidden @ sk_A @ (k3_tarski @ (k2_tarski @ X0 @ sk_B))))
% 4.78/5.03         <= (((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['4', '8'])).
% 4.78/5.03  thf('10', plain,
% 4.78/5.03      (((r2_hidden @ sk_A @ (k3_tarski @ (k1_tarski @ sk_B))))
% 4.78/5.03         <= (((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('sup+', [status(thm)], ['2', '9'])).
% 4.78/5.03  thf(l1_zfmisc_1, axiom,
% 4.78/5.03    (![A:$i,B:$i]:
% 4.78/5.03     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 4.78/5.03  thf('11', plain,
% 4.78/5.03      (![X36 : $i, X38 : $i]:
% 4.78/5.03         ((r1_tarski @ (k1_tarski @ X36) @ X38) | ~ (r2_hidden @ X36 @ X38))),
% 4.78/5.03      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 4.78/5.03  thf('12', plain,
% 4.78/5.03      (((r1_tarski @ (k1_tarski @ sk_A) @ (k3_tarski @ (k1_tarski @ sk_B))))
% 4.78/5.03         <= (((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['10', '11'])).
% 4.78/5.03  thf(t29_ordinal1, axiom,
% 4.78/5.03    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 4.78/5.03  thf('13', plain,
% 4.78/5.03      (![X70 : $i]:
% 4.78/5.03         ((v3_ordinal1 @ (k1_ordinal1 @ X70)) | ~ (v3_ordinal1 @ X70))),
% 4.78/5.03      inference('cnf', [status(esa)], [t29_ordinal1])).
% 4.78/5.03  thf(t26_ordinal1, axiom,
% 4.78/5.03    (![A:$i]:
% 4.78/5.03     ( ( v3_ordinal1 @ A ) =>
% 4.78/5.03       ( ![B:$i]:
% 4.78/5.03         ( ( v3_ordinal1 @ B ) =>
% 4.78/5.03           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 4.78/5.03  thf('14', plain,
% 4.78/5.03      (![X68 : $i, X69 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X68)
% 4.78/5.03          | (r1_ordinal1 @ X69 @ X68)
% 4.78/5.03          | (r2_hidden @ X68 @ X69)
% 4.78/5.03          | ~ (v3_ordinal1 @ X69))),
% 4.78/5.03      inference('cnf', [status(esa)], [t26_ordinal1])).
% 4.78/5.03  thf(d1_ordinal1, axiom,
% 4.78/5.03    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 4.78/5.03  thf('15', plain,
% 4.78/5.03      (![X63 : $i]:
% 4.78/5.03         ((k1_ordinal1 @ X63) = (k2_xboole_0 @ X63 @ (k1_tarski @ X63)))),
% 4.78/5.03      inference('cnf', [status(esa)], [d1_ordinal1])).
% 4.78/5.03  thf('16', plain,
% 4.78/5.03      (![X39 : $i, X40 : $i]:
% 4.78/5.03         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 4.78/5.03      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.78/5.03  thf('17', plain,
% 4.78/5.03      (![X63 : $i]:
% 4.78/5.03         ((k1_ordinal1 @ X63)
% 4.78/5.03           = (k3_tarski @ (k2_tarski @ X63 @ (k1_tarski @ X63))))),
% 4.78/5.03      inference('demod', [status(thm)], ['15', '16'])).
% 4.78/5.03  thf('18', plain,
% 4.78/5.03      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X6 @ X4)
% 4.78/5.03          | (r2_hidden @ X6 @ X5)
% 4.78/5.03          | (r2_hidden @ X6 @ X3)
% 4.78/5.03          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 4.78/5.03      inference('cnf', [status(esa)], [d3_xboole_0])).
% 4.78/5.03  thf('19', plain,
% 4.78/5.03      (![X3 : $i, X5 : $i, X6 : $i]:
% 4.78/5.03         ((r2_hidden @ X6 @ X3)
% 4.78/5.03          | (r2_hidden @ X6 @ X5)
% 4.78/5.03          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['18'])).
% 4.78/5.03  thf('20', plain,
% 4.78/5.03      (![X39 : $i, X40 : $i]:
% 4.78/5.03         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 4.78/5.03      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.78/5.03  thf('21', plain,
% 4.78/5.03      (![X3 : $i, X5 : $i, X6 : $i]:
% 4.78/5.03         ((r2_hidden @ X6 @ X3)
% 4.78/5.03          | (r2_hidden @ X6 @ X5)
% 4.78/5.03          | ~ (r2_hidden @ X6 @ (k3_tarski @ (k2_tarski @ X5 @ X3))))),
% 4.78/5.03      inference('demod', [status(thm)], ['19', '20'])).
% 4.78/5.03  thf('22', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 4.78/5.03          | (r2_hidden @ X1 @ X0)
% 4.78/5.03          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['17', '21'])).
% 4.78/5.03  thf('23', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 4.78/5.03          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 4.78/5.03          | ~ (v3_ordinal1 @ X1)
% 4.78/5.03          | (r2_hidden @ X1 @ (k1_tarski @ X0))
% 4.78/5.03          | (r2_hidden @ X1 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['14', '22'])).
% 4.78/5.03  thf('24', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X0)
% 4.78/5.03          | (r2_hidden @ X1 @ X0)
% 4.78/5.03          | (r2_hidden @ X1 @ (k1_tarski @ X0))
% 4.78/5.03          | ~ (v3_ordinal1 @ X1)
% 4.78/5.03          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1))),
% 4.78/5.03      inference('sup-', [status(thm)], ['13', '23'])).
% 4.78/5.03  thf(t7_ordinal1, axiom,
% 4.78/5.03    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.78/5.03  thf('25', plain,
% 4.78/5.03      (![X71 : $i, X72 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 4.78/5.03      inference('cnf', [status(esa)], [t7_ordinal1])).
% 4.78/5.03  thf('26', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         ((r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 4.78/5.03          | ~ (v3_ordinal1 @ X1)
% 4.78/5.03          | (r2_hidden @ X1 @ X0)
% 4.78/5.03          | ~ (v3_ordinal1 @ X0)
% 4.78/5.03          | ~ (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 4.78/5.03      inference('sup-', [status(thm)], ['24', '25'])).
% 4.78/5.03  thf('27', plain,
% 4.78/5.03      (((~ (v3_ordinal1 @ sk_A)
% 4.78/5.03         | (r2_hidden @ (k3_tarski @ (k1_tarski @ sk_B)) @ sk_A)
% 4.78/5.03         | ~ (v3_ordinal1 @ (k3_tarski @ (k1_tarski @ sk_B)))
% 4.78/5.03         | (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ 
% 4.78/5.03            (k3_tarski @ (k1_tarski @ sk_B)))))
% 4.78/5.03         <= (((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['12', '26'])).
% 4.78/5.03  thf('28', plain, ((v3_ordinal1 @ sk_A)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('29', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 4.78/5.03      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.78/5.03  thf('30', plain,
% 4.78/5.03      (![X3 : $i, X5 : $i, X7 : $i]:
% 4.78/5.03         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 4.78/5.03          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [d3_xboole_0])).
% 4.78/5.03  thf('31', plain,
% 4.78/5.03      (![X39 : $i, X40 : $i]:
% 4.78/5.03         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 4.78/5.03      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.78/5.03  thf('32', plain,
% 4.78/5.03      (![X3 : $i, X5 : $i, X7 : $i]:
% 4.78/5.03         (((X7) = (k3_tarski @ (k2_tarski @ X5 @ X3)))
% 4.78/5.03          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 4.78/5.03      inference('demod', [status(thm)], ['30', '31'])).
% 4.78/5.03  thf('33', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 4.78/5.03          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X0)
% 4.78/5.03          | ((X1) = (k3_tarski @ (k2_tarski @ X0 @ X0))))),
% 4.78/5.03      inference('eq_fact', [status(thm)], ['32'])).
% 4.78/5.03  thf('34', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (((X0) = (k3_tarski @ (k2_tarski @ X0 @ X0)))
% 4.78/5.03          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 4.78/5.03      inference('eq_fact', [status(thm)], ['33'])).
% 4.78/5.03  thf('35', plain,
% 4.78/5.03      (![X3 : $i, X5 : $i, X7 : $i]:
% 4.78/5.03         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 4.78/5.03          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 4.78/5.03          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [d3_xboole_0])).
% 4.78/5.03  thf('36', plain,
% 4.78/5.03      (![X39 : $i, X40 : $i]:
% 4.78/5.03         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 4.78/5.03      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.78/5.03  thf('37', plain,
% 4.78/5.03      (![X3 : $i, X5 : $i, X7 : $i]:
% 4.78/5.03         (((X7) = (k3_tarski @ (k2_tarski @ X5 @ X3)))
% 4.78/5.03          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 4.78/5.03          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 4.78/5.03      inference('demod', [status(thm)], ['35', '36'])).
% 4.78/5.03  thf('38', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (((X0) = (k3_tarski @ (k2_tarski @ X0 @ X0)))
% 4.78/5.03          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 4.78/5.03          | ((X0) = (k3_tarski @ (k2_tarski @ X0 @ X0))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['34', '37'])).
% 4.78/5.03  thf('39', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 4.78/5.03          | ((X0) = (k3_tarski @ (k2_tarski @ X0 @ X0))))),
% 4.78/5.03      inference('simplify', [status(thm)], ['38'])).
% 4.78/5.03  thf('40', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (((X0) = (k3_tarski @ (k2_tarski @ X0 @ X0)))
% 4.78/5.03          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 4.78/5.03      inference('eq_fact', [status(thm)], ['33'])).
% 4.78/5.03  thf('41', plain, (![X0 : $i]: ((X0) = (k3_tarski @ (k2_tarski @ X0 @ X0)))),
% 4.78/5.03      inference('clc', [status(thm)], ['39', '40'])).
% 4.78/5.03  thf('42', plain, (![X0 : $i]: ((X0) = (k3_tarski @ (k1_tarski @ X0)))),
% 4.78/5.03      inference('sup+', [status(thm)], ['29', '41'])).
% 4.78/5.03  thf('43', plain, (![X0 : $i]: ((X0) = (k3_tarski @ (k1_tarski @ X0)))),
% 4.78/5.03      inference('sup+', [status(thm)], ['29', '41'])).
% 4.78/5.03  thf('44', plain, ((v3_ordinal1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('45', plain, (![X0 : $i]: ((X0) = (k3_tarski @ (k1_tarski @ X0)))),
% 4.78/5.03      inference('sup+', [status(thm)], ['29', '41'])).
% 4.78/5.03  thf('46', plain,
% 4.78/5.03      ((((r2_hidden @ sk_B @ sk_A)
% 4.78/5.03         | (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 4.78/5.03         <= (((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('demod', [status(thm)], ['27', '28', '42', '43', '44', '45'])).
% 4.78/5.03  thf('47', plain,
% 4.78/5.03      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('split', [status(esa)], ['3'])).
% 4.78/5.03  thf(antisymmetry_r2_hidden, axiom,
% 4.78/5.03    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 4.78/5.03  thf('48', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 4.78/5.03      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 4.78/5.03  thf('49', plain,
% 4.78/5.03      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['47', '48'])).
% 4.78/5.03  thf('50', plain,
% 4.78/5.03      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 4.78/5.03         <= (((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('clc', [status(thm)], ['46', '49'])).
% 4.78/5.03  thf('51', plain,
% 4.78/5.03      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 4.78/5.03         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('split', [status(esa)], ['0'])).
% 4.78/5.03  thf('52', plain,
% 4.78/5.03      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 4.78/5.03       ~ ((r2_hidden @ sk_A @ sk_B))),
% 4.78/5.03      inference('sup-', [status(thm)], ['50', '51'])).
% 4.78/5.03  thf('53', plain,
% 4.78/5.03      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 4.78/5.03       ((r2_hidden @ sk_A @ sk_B))),
% 4.78/5.03      inference('split', [status(esa)], ['3'])).
% 4.78/5.03  thf('54', plain,
% 4.78/5.03      (![X68 : $i, X69 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X68)
% 4.78/5.03          | (r1_ordinal1 @ X69 @ X68)
% 4.78/5.03          | (r2_hidden @ X68 @ X69)
% 4.78/5.03          | ~ (v3_ordinal1 @ X69))),
% 4.78/5.03      inference('cnf', [status(esa)], [t26_ordinal1])).
% 4.78/5.03  thf('55', plain,
% 4.78/5.03      (![X68 : $i, X69 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X68)
% 4.78/5.03          | (r1_ordinal1 @ X69 @ X68)
% 4.78/5.03          | (r2_hidden @ X68 @ X69)
% 4.78/5.03          | ~ (v3_ordinal1 @ X69))),
% 4.78/5.03      inference('cnf', [status(esa)], [t26_ordinal1])).
% 4.78/5.03  thf('56', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 4.78/5.03      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 4.78/5.03  thf('57', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X0)
% 4.78/5.03          | (r1_ordinal1 @ X0 @ X1)
% 4.78/5.03          | ~ (v3_ordinal1 @ X1)
% 4.78/5.03          | ~ (r2_hidden @ X0 @ X1))),
% 4.78/5.03      inference('sup-', [status(thm)], ['55', '56'])).
% 4.78/5.03  thf('58', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X0)
% 4.78/5.03          | (r1_ordinal1 @ X0 @ X1)
% 4.78/5.03          | ~ (v3_ordinal1 @ X1)
% 4.78/5.03          | ~ (v3_ordinal1 @ X0)
% 4.78/5.03          | (r1_ordinal1 @ X1 @ X0)
% 4.78/5.03          | ~ (v3_ordinal1 @ X1))),
% 4.78/5.03      inference('sup-', [status(thm)], ['54', '57'])).
% 4.78/5.03  thf('59', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         ((r1_ordinal1 @ X1 @ X0)
% 4.78/5.03          | ~ (v3_ordinal1 @ X1)
% 4.78/5.03          | (r1_ordinal1 @ X0 @ X1)
% 4.78/5.03          | ~ (v3_ordinal1 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['58'])).
% 4.78/5.03  thf('60', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 4.78/5.03      inference('eq_fact', [status(thm)], ['59'])).
% 4.78/5.03  thf('61', plain,
% 4.78/5.03      (![X0 : $i]: ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['60'])).
% 4.78/5.03  thf(redefinition_r1_ordinal1, axiom,
% 4.78/5.03    (![A:$i,B:$i]:
% 4.78/5.03     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 4.78/5.03       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 4.78/5.03  thf('62', plain,
% 4.78/5.03      (![X64 : $i, X65 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X64)
% 4.78/5.03          | ~ (v3_ordinal1 @ X65)
% 4.78/5.03          | (r1_tarski @ X64 @ X65)
% 4.78/5.03          | ~ (r1_ordinal1 @ X64 @ X65))),
% 4.78/5.03      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 4.78/5.03  thf('63', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X0)
% 4.78/5.03          | (r1_tarski @ X0 @ X0)
% 4.78/5.03          | ~ (v3_ordinal1 @ X0)
% 4.78/5.03          | ~ (v3_ordinal1 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['61', '62'])).
% 4.78/5.03  thf('64', plain,
% 4.78/5.03      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['63'])).
% 4.78/5.03  thf('65', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 4.78/5.03      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.78/5.03  thf('66', plain,
% 4.78/5.03      (![X63 : $i]:
% 4.78/5.03         ((k1_ordinal1 @ X63)
% 4.78/5.03           = (k3_tarski @ (k2_tarski @ X63 @ (k1_tarski @ X63))))),
% 4.78/5.03      inference('demod', [status(thm)], ['15', '16'])).
% 4.78/5.03  thf('67', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         ((k1_ordinal1 @ X0)
% 4.78/5.03           = (k3_tarski @ (k2_tarski @ X0 @ (k2_tarski @ X0 @ X0))))),
% 4.78/5.03      inference('sup+', [status(thm)], ['65', '66'])).
% 4.78/5.03  thf('68', plain,
% 4.78/5.03      (![X68 : $i, X69 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X68)
% 4.78/5.03          | (r1_ordinal1 @ X69 @ X68)
% 4.78/5.03          | (r2_hidden @ X68 @ X69)
% 4.78/5.03          | ~ (v3_ordinal1 @ X69))),
% 4.78/5.03      inference('cnf', [status(esa)], [t26_ordinal1])).
% 4.78/5.03  thf('69', plain,
% 4.78/5.03      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X2 @ X5)
% 4.78/5.03          | (r2_hidden @ X2 @ X4)
% 4.78/5.03          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 4.78/5.03      inference('cnf', [status(esa)], [d3_xboole_0])).
% 4.78/5.03  thf('70', plain,
% 4.78/5.03      (![X2 : $i, X3 : $i, X5 : $i]:
% 4.78/5.03         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 4.78/5.03      inference('simplify', [status(thm)], ['69'])).
% 4.78/5.03  thf('71', plain,
% 4.78/5.03      (![X39 : $i, X40 : $i]:
% 4.78/5.03         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 4.78/5.03      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.78/5.03  thf('72', plain,
% 4.78/5.03      (![X2 : $i, X3 : $i, X5 : $i]:
% 4.78/5.03         ((r2_hidden @ X2 @ (k3_tarski @ (k2_tarski @ X5 @ X3)))
% 4.78/5.03          | ~ (r2_hidden @ X2 @ X5))),
% 4.78/5.03      inference('demod', [status(thm)], ['70', '71'])).
% 4.78/5.03  thf('73', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X0)
% 4.78/5.03          | (r1_ordinal1 @ X0 @ X1)
% 4.78/5.03          | ~ (v3_ordinal1 @ X1)
% 4.78/5.03          | (r2_hidden @ X1 @ (k3_tarski @ (k2_tarski @ X0 @ X2))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['68', '72'])).
% 4.78/5.03  thf('74', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 4.78/5.03          | ~ (v3_ordinal1 @ X1)
% 4.78/5.03          | (r1_ordinal1 @ X0 @ X1)
% 4.78/5.03          | ~ (v3_ordinal1 @ X0))),
% 4.78/5.03      inference('sup+', [status(thm)], ['67', '73'])).
% 4.78/5.03  thf('75', plain,
% 4.78/5.03      (![X71 : $i, X72 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 4.78/5.03      inference('cnf', [status(esa)], [t7_ordinal1])).
% 4.78/5.03  thf('76', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X0)
% 4.78/5.03          | (r1_ordinal1 @ X0 @ X1)
% 4.78/5.03          | ~ (v3_ordinal1 @ X1)
% 4.78/5.03          | ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X1))),
% 4.78/5.03      inference('sup-', [status(thm)], ['74', '75'])).
% 4.78/5.03  thf('77', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 4.78/5.03          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 4.78/5.03          | (r1_ordinal1 @ X0 @ (k1_ordinal1 @ X0))
% 4.78/5.03          | ~ (v3_ordinal1 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['64', '76'])).
% 4.78/5.03  thf('78', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X0)
% 4.78/5.03          | (r1_ordinal1 @ X0 @ (k1_ordinal1 @ X0))
% 4.78/5.03          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['77'])).
% 4.78/5.03  thf('79', plain,
% 4.78/5.03      (![X70 : $i]:
% 4.78/5.03         ((v3_ordinal1 @ (k1_ordinal1 @ X70)) | ~ (v3_ordinal1 @ X70))),
% 4.78/5.03      inference('cnf', [status(esa)], [t29_ordinal1])).
% 4.78/5.03  thf('80', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         ((r1_ordinal1 @ X0 @ (k1_ordinal1 @ X0)) | ~ (v3_ordinal1 @ X0))),
% 4.78/5.03      inference('clc', [status(thm)], ['78', '79'])).
% 4.78/5.03  thf('81', plain,
% 4.78/5.03      (![X64 : $i, X65 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X64)
% 4.78/5.03          | ~ (v3_ordinal1 @ X65)
% 4.78/5.03          | (r1_tarski @ X64 @ X65)
% 4.78/5.03          | ~ (r1_ordinal1 @ X64 @ X65))),
% 4.78/5.03      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 4.78/5.03  thf('82', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X0)
% 4.78/5.03          | (r1_tarski @ X0 @ (k1_ordinal1 @ X0))
% 4.78/5.03          | ~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 4.78/5.03          | ~ (v3_ordinal1 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['80', '81'])).
% 4.78/5.03  thf('83', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 4.78/5.03          | (r1_tarski @ X0 @ (k1_ordinal1 @ X0))
% 4.78/5.03          | ~ (v3_ordinal1 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['82'])).
% 4.78/5.03  thf('84', plain,
% 4.78/5.03      (![X70 : $i]:
% 4.78/5.03         ((v3_ordinal1 @ (k1_ordinal1 @ X70)) | ~ (v3_ordinal1 @ X70))),
% 4.78/5.03      inference('cnf', [status(esa)], [t29_ordinal1])).
% 4.78/5.03  thf('85', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X0) | (r1_tarski @ X0 @ (k1_ordinal1 @ X0)))),
% 4.78/5.03      inference('clc', [status(thm)], ['83', '84'])).
% 4.78/5.03  thf('86', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         ((k1_ordinal1 @ X0)
% 4.78/5.03           = (k3_tarski @ (k2_tarski @ X0 @ (k2_tarski @ X0 @ X0))))),
% 4.78/5.03      inference('sup+', [status(thm)], ['65', '66'])).
% 4.78/5.03  thf('87', plain,
% 4.78/5.03      (![X68 : $i, X69 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X68)
% 4.78/5.03          | (r1_ordinal1 @ X69 @ X68)
% 4.78/5.03          | (r2_hidden @ X68 @ X69)
% 4.78/5.03          | ~ (v3_ordinal1 @ X69))),
% 4.78/5.03      inference('cnf', [status(esa)], [t26_ordinal1])).
% 4.78/5.03  thf('88', plain,
% 4.78/5.03      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('split', [status(esa)], ['0'])).
% 4.78/5.03  thf('89', plain,
% 4.78/5.03      (((~ (v3_ordinal1 @ sk_B)
% 4.78/5.03         | (r1_ordinal1 @ sk_B @ sk_A)
% 4.78/5.03         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['87', '88'])).
% 4.78/5.03  thf('90', plain, ((v3_ordinal1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('91', plain, ((v3_ordinal1 @ sk_A)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('92', plain,
% 4.78/5.03      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('demod', [status(thm)], ['89', '90', '91'])).
% 4.78/5.03  thf('93', plain,
% 4.78/5.03      (![X64 : $i, X65 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X64)
% 4.78/5.03          | ~ (v3_ordinal1 @ X65)
% 4.78/5.03          | (r1_tarski @ X64 @ X65)
% 4.78/5.03          | ~ (r1_ordinal1 @ X64 @ X65))),
% 4.78/5.03      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 4.78/5.03  thf('94', plain,
% 4.78/5.03      ((((r1_tarski @ sk_B @ sk_A)
% 4.78/5.03         | ~ (v3_ordinal1 @ sk_A)
% 4.78/5.03         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['92', '93'])).
% 4.78/5.03  thf('95', plain, ((v3_ordinal1 @ sk_A)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('96', plain, ((v3_ordinal1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('97', plain,
% 4.78/5.03      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('demod', [status(thm)], ['94', '95', '96'])).
% 4.78/5.03  thf(t24_ordinal1, axiom,
% 4.78/5.03    (![A:$i]:
% 4.78/5.03     ( ( v3_ordinal1 @ A ) =>
% 4.78/5.03       ( ![B:$i]:
% 4.78/5.03         ( ( v3_ordinal1 @ B ) =>
% 4.78/5.03           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 4.78/5.03                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 4.78/5.03  thf('98', plain,
% 4.78/5.03      (![X66 : $i, X67 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X66)
% 4.78/5.03          | (r2_hidden @ X67 @ X66)
% 4.78/5.03          | ((X67) = (X66))
% 4.78/5.03          | (r2_hidden @ X66 @ X67)
% 4.78/5.03          | ~ (v3_ordinal1 @ X67))),
% 4.78/5.03      inference('cnf', [status(esa)], [t24_ordinal1])).
% 4.78/5.03  thf('99', plain,
% 4.78/5.03      (![X71 : $i, X72 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 4.78/5.03      inference('cnf', [status(esa)], [t7_ordinal1])).
% 4.78/5.03  thf('100', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X1)
% 4.78/5.03          | (r2_hidden @ X0 @ X1)
% 4.78/5.03          | ((X1) = (X0))
% 4.78/5.03          | ~ (v3_ordinal1 @ X0)
% 4.78/5.03          | ~ (r1_tarski @ X0 @ X1))),
% 4.78/5.03      inference('sup-', [status(thm)], ['98', '99'])).
% 4.78/5.03  thf('101', plain,
% 4.78/5.03      (((~ (v3_ordinal1 @ sk_B)
% 4.78/5.03         | ((sk_A) = (sk_B))
% 4.78/5.03         | (r2_hidden @ sk_B @ sk_A)
% 4.78/5.03         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['97', '100'])).
% 4.78/5.03  thf('102', plain, ((v3_ordinal1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('103', plain, ((v3_ordinal1 @ sk_A)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('104', plain,
% 4.78/5.03      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_B @ sk_A)))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('demod', [status(thm)], ['101', '102', '103'])).
% 4.78/5.03  thf('105', plain,
% 4.78/5.03      (![X2 : $i, X3 : $i, X5 : $i]:
% 4.78/5.03         ((r2_hidden @ X2 @ (k3_tarski @ (k2_tarski @ X5 @ X3)))
% 4.78/5.03          | ~ (r2_hidden @ X2 @ X5))),
% 4.78/5.03      inference('demod', [status(thm)], ['70', '71'])).
% 4.78/5.03  thf('106', plain,
% 4.78/5.03      ((![X0 : $i]:
% 4.78/5.03          (((sk_A) = (sk_B))
% 4.78/5.03           | (r2_hidden @ sk_B @ (k3_tarski @ (k2_tarski @ sk_A @ X0)))))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['104', '105'])).
% 4.78/5.03  thf('107', plain,
% 4.78/5.03      ((((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A)) | ((sk_A) = (sk_B))))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('sup+', [status(thm)], ['86', '106'])).
% 4.78/5.03  thf('108', plain,
% 4.78/5.03      (![X70 : $i]:
% 4.78/5.03         ((v3_ordinal1 @ (k1_ordinal1 @ X70)) | ~ (v3_ordinal1 @ X70))),
% 4.78/5.03      inference('cnf', [status(esa)], [t29_ordinal1])).
% 4.78/5.03  thf('109', plain,
% 4.78/5.03      (![X70 : $i]:
% 4.78/5.03         ((v3_ordinal1 @ (k1_ordinal1 @ X70)) | ~ (v3_ordinal1 @ X70))),
% 4.78/5.03      inference('cnf', [status(esa)], [t29_ordinal1])).
% 4.78/5.03  thf('110', plain,
% 4.78/5.03      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 4.78/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('split', [status(esa)], ['3'])).
% 4.78/5.03  thf('111', plain,
% 4.78/5.03      (![X64 : $i, X65 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X64)
% 4.78/5.03          | ~ (v3_ordinal1 @ X65)
% 4.78/5.03          | (r1_tarski @ X64 @ X65)
% 4.78/5.03          | ~ (r1_ordinal1 @ X64 @ X65))),
% 4.78/5.03      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 4.78/5.03  thf('112', plain,
% 4.78/5.03      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 4.78/5.03         | ~ (v3_ordinal1 @ sk_B)
% 4.78/5.03         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 4.78/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['110', '111'])).
% 4.78/5.03  thf('113', plain, ((v3_ordinal1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('114', plain,
% 4.78/5.03      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 4.78/5.03         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 4.78/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('demod', [status(thm)], ['112', '113'])).
% 4.78/5.03  thf('115', plain,
% 4.78/5.03      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 4.78/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['109', '114'])).
% 4.78/5.03  thf('116', plain, ((v3_ordinal1 @ sk_A)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('117', plain,
% 4.78/5.03      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 4.78/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('demod', [status(thm)], ['115', '116'])).
% 4.78/5.03  thf('118', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X1)
% 4.78/5.03          | (r2_hidden @ X0 @ X1)
% 4.78/5.03          | ((X1) = (X0))
% 4.78/5.03          | ~ (v3_ordinal1 @ X0)
% 4.78/5.03          | ~ (r1_tarski @ X0 @ X1))),
% 4.78/5.03      inference('sup-', [status(thm)], ['98', '99'])).
% 4.78/5.03  thf('119', plain,
% 4.78/5.03      (((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 4.78/5.03         | ((sk_B) = (k1_ordinal1 @ sk_A))
% 4.78/5.03         | (r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)
% 4.78/5.03         | ~ (v3_ordinal1 @ sk_B)))
% 4.78/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['117', '118'])).
% 4.78/5.03  thf('120', plain, ((v3_ordinal1 @ sk_B)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('121', plain,
% 4.78/5.03      (((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 4.78/5.03         | ((sk_B) = (k1_ordinal1 @ sk_A))
% 4.78/5.03         | (r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 4.78/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('demod', [status(thm)], ['119', '120'])).
% 4.78/5.03  thf('122', plain,
% 4.78/5.03      (((~ (v3_ordinal1 @ sk_A)
% 4.78/5.03         | (r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)
% 4.78/5.03         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 4.78/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['108', '121'])).
% 4.78/5.03  thf('123', plain, ((v3_ordinal1 @ sk_A)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('124', plain,
% 4.78/5.03      ((((r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)
% 4.78/5.03         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 4.78/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('demod', [status(thm)], ['122', '123'])).
% 4.78/5.03  thf('125', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 4.78/5.03      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 4.78/5.03  thf('126', plain,
% 4.78/5.03      (((((sk_B) = (k1_ordinal1 @ sk_A))
% 4.78/5.03         | ~ (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))))
% 4.78/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['124', '125'])).
% 4.78/5.03  thf('127', plain,
% 4.78/5.03      (((((sk_A) = (sk_B)) | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 4.78/5.03             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['107', '126'])).
% 4.78/5.03  thf('128', plain,
% 4.78/5.03      ((((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A)) | ((sk_A) = (sk_B))))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('sup+', [status(thm)], ['86', '106'])).
% 4.78/5.03  thf('129', plain,
% 4.78/5.03      ((((r2_hidden @ sk_B @ sk_B) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B))))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 4.78/5.03             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('sup+', [status(thm)], ['127', '128'])).
% 4.78/5.03  thf('130', plain,
% 4.78/5.03      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_B @ sk_B)))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 4.78/5.03             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['129'])).
% 4.78/5.03  thf('131', plain,
% 4.78/5.03      (((((sk_A) = (sk_B)) | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 4.78/5.03             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['107', '126'])).
% 4.78/5.03  thf('132', plain,
% 4.78/5.03      ((((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A)) | ((sk_A) = (sk_B))))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('sup+', [status(thm)], ['86', '106'])).
% 4.78/5.03  thf('133', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 4.78/5.03      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 4.78/5.03  thf('134', plain,
% 4.78/5.03      (((((sk_A) = (sk_B)) | ~ (r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['132', '133'])).
% 4.78/5.03  thf('135', plain,
% 4.78/5.03      (((~ (r2_hidden @ sk_B @ sk_B) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B))))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 4.78/5.03             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['131', '134'])).
% 4.78/5.03  thf('136', plain,
% 4.78/5.03      (((((sk_A) = (sk_B)) | ~ (r2_hidden @ sk_B @ sk_B)))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 4.78/5.03             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['135'])).
% 4.78/5.03  thf('137', plain,
% 4.78/5.03      ((((sk_A) = (sk_B)))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 4.78/5.03             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('clc', [status(thm)], ['130', '136'])).
% 4.78/5.03  thf('138', plain,
% 4.78/5.03      ((((r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)
% 4.78/5.03         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 4.78/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('demod', [status(thm)], ['122', '123'])).
% 4.78/5.03  thf('139', plain,
% 4.78/5.03      (![X71 : $i, X72 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 4.78/5.03      inference('cnf', [status(esa)], [t7_ordinal1])).
% 4.78/5.03  thf('140', plain,
% 4.78/5.03      (((((sk_B) = (k1_ordinal1 @ sk_A))
% 4.78/5.03         | ~ (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))))
% 4.78/5.03         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['138', '139'])).
% 4.78/5.03  thf('141', plain,
% 4.78/5.03      (((~ (r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 4.78/5.03         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 4.78/5.03             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['137', '140'])).
% 4.78/5.03  thf('142', plain,
% 4.78/5.03      ((((sk_A) = (sk_B)))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 4.78/5.03             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('clc', [status(thm)], ['130', '136'])).
% 4.78/5.03  thf('143', plain,
% 4.78/5.03      (((~ (r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 4.78/5.03         | ((sk_A) = (k1_ordinal1 @ sk_A))))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 4.78/5.03             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('demod', [status(thm)], ['141', '142'])).
% 4.78/5.03  thf('144', plain,
% 4.78/5.03      (((~ (v3_ordinal1 @ sk_A) | ((sk_A) = (k1_ordinal1 @ sk_A))))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 4.78/5.03             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['85', '143'])).
% 4.78/5.03  thf('145', plain, ((v3_ordinal1 @ sk_A)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('146', plain,
% 4.78/5.03      ((((sk_A) = (k1_ordinal1 @ sk_A)))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 4.78/5.03             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('demod', [status(thm)], ['144', '145'])).
% 4.78/5.03  thf('147', plain,
% 4.78/5.03      (![X63 : $i]:
% 4.78/5.03         ((k1_ordinal1 @ X63)
% 4.78/5.03           = (k3_tarski @ (k2_tarski @ X63 @ (k1_tarski @ X63))))),
% 4.78/5.03      inference('demod', [status(thm)], ['15', '16'])).
% 4.78/5.03  thf(t70_enumset1, axiom,
% 4.78/5.03    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 4.78/5.03  thf('148', plain,
% 4.78/5.03      (![X9 : $i, X10 : $i]:
% 4.78/5.03         ((k1_enumset1 @ X9 @ X9 @ X10) = (k2_tarski @ X9 @ X10))),
% 4.78/5.03      inference('cnf', [status(esa)], [t70_enumset1])).
% 4.78/5.03  thf('149', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 4.78/5.03      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.78/5.03  thf('150', plain,
% 4.78/5.03      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 4.78/5.03      inference('sup+', [status(thm)], ['148', '149'])).
% 4.78/5.03  thf(t71_enumset1, axiom,
% 4.78/5.03    (![A:$i,B:$i,C:$i]:
% 4.78/5.03     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 4.78/5.03  thf('151', plain,
% 4.78/5.03      (![X11 : $i, X12 : $i, X13 : $i]:
% 4.78/5.03         ((k2_enumset1 @ X11 @ X11 @ X12 @ X13)
% 4.78/5.03           = (k1_enumset1 @ X11 @ X12 @ X13))),
% 4.78/5.03      inference('cnf', [status(esa)], [t71_enumset1])).
% 4.78/5.03  thf(t72_enumset1, axiom,
% 4.78/5.03    (![A:$i,B:$i,C:$i,D:$i]:
% 4.78/5.03     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 4.78/5.03  thf('152', plain,
% 4.78/5.03      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 4.78/5.03         ((k3_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17)
% 4.78/5.03           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 4.78/5.03      inference('cnf', [status(esa)], [t72_enumset1])).
% 4.78/5.03  thf(t73_enumset1, axiom,
% 4.78/5.03    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 4.78/5.03     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 4.78/5.03       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 4.78/5.03  thf('153', plain,
% 4.78/5.03      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 4.78/5.03         ((k4_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22)
% 4.78/5.03           = (k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22))),
% 4.78/5.03      inference('cnf', [status(esa)], [t73_enumset1])).
% 4.78/5.03  thf(t74_enumset1, axiom,
% 4.78/5.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.78/5.03     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 4.78/5.03       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 4.78/5.03  thf('154', plain,
% 4.78/5.03      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 4.78/5.03         ((k5_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 4.78/5.03           = (k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 4.78/5.03      inference('cnf', [status(esa)], [t74_enumset1])).
% 4.78/5.03  thf(t75_enumset1, axiom,
% 4.78/5.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 4.78/5.03     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 4.78/5.03       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 4.78/5.03  thf('155', plain,
% 4.78/5.03      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 4.78/5.03         ((k6_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)
% 4.78/5.03           = (k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35))),
% 4.78/5.03      inference('cnf', [status(esa)], [t75_enumset1])).
% 4.78/5.03  thf(d6_enumset1, axiom,
% 4.78/5.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 4.78/5.03     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 4.78/5.03       ( ![J:$i]:
% 4.78/5.03         ( ( r2_hidden @ J @ I ) <=>
% 4.78/5.03           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 4.78/5.03                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 4.78/5.03                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 4.78/5.03  thf(zf_stmt_1, type, zip_tseitin_0 :
% 4.78/5.03      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 4.78/5.03  thf(zf_stmt_2, axiom,
% 4.78/5.03    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 4.78/5.03     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 4.78/5.03       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 4.78/5.03         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 4.78/5.03         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 4.78/5.03  thf(zf_stmt_3, axiom,
% 4.78/5.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 4.78/5.03     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 4.78/5.03       ( ![J:$i]:
% 4.78/5.03         ( ( r2_hidden @ J @ I ) <=>
% 4.78/5.03           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 4.78/5.03  thf('156', plain,
% 4.78/5.03      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, 
% 4.78/5.03         X58 : $i, X59 : $i, X60 : $i]:
% 4.78/5.03         ((zip_tseitin_0 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59)
% 4.78/5.03          | (r2_hidden @ X51 @ X60)
% 4.78/5.03          | ((X60)
% 4.78/5.03              != (k6_enumset1 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52)))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.78/5.03  thf('157', plain,
% 4.78/5.03      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, 
% 4.78/5.03         X58 : $i, X59 : $i]:
% 4.78/5.03         ((r2_hidden @ X51 @ 
% 4.78/5.03           (k6_enumset1 @ X59 @ X58 @ X57 @ X56 @ X55 @ X54 @ X53 @ X52))
% 4.78/5.03          | (zip_tseitin_0 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ 
% 4.78/5.03             X59))),
% 4.78/5.03      inference('simplify', [status(thm)], ['156'])).
% 4.78/5.03  thf('158', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 4.78/5.03         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 4.78/5.03          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 4.78/5.03      inference('sup+', [status(thm)], ['155', '157'])).
% 4.78/5.03  thf('159', plain,
% 4.78/5.03      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, 
% 4.78/5.03         X48 : $i, X49 : $i]:
% 4.78/5.03         (((X42) != (X41))
% 4.78/5.03          | ~ (zip_tseitin_0 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ 
% 4.78/5.03               X41))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.78/5.03  thf('160', plain,
% 4.78/5.03      (![X41 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, 
% 4.78/5.03         X49 : $i]:
% 4.78/5.03         ~ (zip_tseitin_0 @ X41 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X41)),
% 4.78/5.03      inference('simplify', [status(thm)], ['159'])).
% 4.78/5.03  thf('161', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 4.78/5.03         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 4.78/5.03      inference('sup-', [status(thm)], ['158', '160'])).
% 4.78/5.03  thf('162', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 4.78/5.03         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 4.78/5.03      inference('sup+', [status(thm)], ['154', '161'])).
% 4.78/5.03  thf('163', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.78/5.03         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 4.78/5.03      inference('sup+', [status(thm)], ['153', '162'])).
% 4.78/5.03  thf('164', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.78/5.03         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 4.78/5.03      inference('sup+', [status(thm)], ['152', '163'])).
% 4.78/5.03  thf('165', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 4.78/5.03      inference('sup+', [status(thm)], ['151', '164'])).
% 4.78/5.03  thf('166', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.78/5.03      inference('sup+', [status(thm)], ['150', '165'])).
% 4.78/5.03  thf('167', plain,
% 4.78/5.03      (![X2 : $i, X3 : $i, X5 : $i]:
% 4.78/5.03         ((r2_hidden @ X2 @ (k3_tarski @ (k2_tarski @ X5 @ X3)))
% 4.78/5.03          | ~ (r2_hidden @ X2 @ X3))),
% 4.78/5.03      inference('demod', [status(thm)], ['6', '7'])).
% 4.78/5.03  thf('168', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ (k1_tarski @ X0))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['166', '167'])).
% 4.78/5.03  thf('169', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 4.78/5.03      inference('sup+', [status(thm)], ['147', '168'])).
% 4.78/5.03  thf('170', plain,
% 4.78/5.03      (![X71 : $i, X72 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X71 @ X72) | ~ (r1_tarski @ X72 @ X71))),
% 4.78/5.03      inference('cnf', [status(esa)], [t7_ordinal1])).
% 4.78/5.03  thf('171', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 4.78/5.03      inference('sup-', [status(thm)], ['169', '170'])).
% 4.78/5.03  thf('172', plain,
% 4.78/5.03      ((~ (r1_tarski @ sk_A @ sk_A))
% 4.78/5.03         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 4.78/5.03             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['146', '171'])).
% 4.78/5.03  thf('173', plain, ((v3_ordinal1 @ sk_A)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('174', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         ((r1_ordinal1 @ X1 @ X0)
% 4.78/5.03          | ~ (v3_ordinal1 @ X1)
% 4.78/5.03          | (r1_ordinal1 @ X0 @ X1)
% 4.78/5.03          | ~ (v3_ordinal1 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['58'])).
% 4.78/5.03  thf('175', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X0)
% 4.78/5.03          | (r1_ordinal1 @ X0 @ sk_A)
% 4.78/5.03          | (r1_ordinal1 @ sk_A @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['173', '174'])).
% 4.78/5.03  thf('176', plain, (((r1_ordinal1 @ sk_A @ sk_A) | ~ (v3_ordinal1 @ sk_A))),
% 4.78/5.03      inference('eq_fact', [status(thm)], ['175'])).
% 4.78/5.03  thf('177', plain, ((v3_ordinal1 @ sk_A)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('178', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 4.78/5.03      inference('demod', [status(thm)], ['176', '177'])).
% 4.78/5.03  thf('179', plain,
% 4.78/5.03      (![X64 : $i, X65 : $i]:
% 4.78/5.03         (~ (v3_ordinal1 @ X64)
% 4.78/5.03          | ~ (v3_ordinal1 @ X65)
% 4.78/5.03          | (r1_tarski @ X64 @ X65)
% 4.78/5.03          | ~ (r1_ordinal1 @ X64 @ X65))),
% 4.78/5.03      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 4.78/5.03  thf('180', plain,
% 4.78/5.03      (((r1_tarski @ sk_A @ sk_A)
% 4.78/5.03        | ~ (v3_ordinal1 @ sk_A)
% 4.78/5.03        | ~ (v3_ordinal1 @ sk_A))),
% 4.78/5.03      inference('sup-', [status(thm)], ['178', '179'])).
% 4.78/5.03  thf('181', plain, ((v3_ordinal1 @ sk_A)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('182', plain, ((v3_ordinal1 @ sk_A)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('183', plain, ((r1_tarski @ sk_A @ sk_A)),
% 4.78/5.03      inference('demod', [status(thm)], ['180', '181', '182'])).
% 4.78/5.03  thf('184', plain,
% 4.78/5.03      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 4.78/5.03       ((r2_hidden @ sk_A @ sk_B))),
% 4.78/5.03      inference('demod', [status(thm)], ['172', '183'])).
% 4.78/5.03  thf('185', plain, ($false),
% 4.78/5.03      inference('sat_resolution*', [status(thm)], ['1', '52', '53', '184'])).
% 4.78/5.03  
% 4.78/5.03  % SZS output end Refutation
% 4.78/5.03  
% 4.78/5.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
