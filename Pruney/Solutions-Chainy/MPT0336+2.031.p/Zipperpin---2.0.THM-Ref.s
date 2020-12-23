%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YCGMS78QXd

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:24 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 142 expanded)
%              Number of leaves         :   30 (  54 expanded)
%              Depth                    :   24
%              Number of atoms          :  736 (1149 expanded)
%              Number of equality atoms :   74 ( 101 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

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

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( X19 = X20 )
      | ( X19 = X21 )
      | ( X19 = X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
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

thf('10',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ~ ( zip_tseitin_0 @ X28 @ X24 @ X25 @ X26 )
      | ( X27
       != ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X24 @ X25 @ X26 )
      | ~ ( r2_hidden @ X28 @ ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('22',plain,(
    ! [X52: $i,X53: $i] :
      ( ( r1_tarski @ X52 @ ( k1_tarski @ X53 ) )
      | ( X52
       != ( k1_tarski @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('23',plain,(
    ! [X53: $i] :
      ( r1_tarski @ ( k1_tarski @ X53 ) @ ( k1_tarski @ X53 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','25'])).

thf('27',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X51: $i,X52: $i] :
      ( ( X52
        = ( k1_tarski @ X51 ) )
      | ( X52 = k1_xboole_0 )
      | ~ ( r1_tarski @ X52 @ ( k1_tarski @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('31',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('36',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k1_tarski @ sk_D ) )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','56'])).

thf('58',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_D ) )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','57'])).

thf('59',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('60',plain,
    ( ( ( k1_tarski @ sk_D )
     != k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['59'])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['58','60'])).

thf('62',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('63',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['63'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('65',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ X16 )
      | ( ( k3_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','68'])).

thf('70',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['0','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YCGMS78QXd
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.35/1.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.35/1.56  % Solved by: fo/fo7.sh
% 1.35/1.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.35/1.56  % done 2130 iterations in 1.107s
% 1.35/1.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.35/1.56  % SZS output start Refutation
% 1.35/1.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.35/1.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.35/1.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.35/1.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.35/1.56  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.35/1.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.35/1.56  thf(sk_D_type, type, sk_D: $i).
% 1.35/1.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.35/1.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.35/1.56  thf(sk_B_type, type, sk_B: $i).
% 1.35/1.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.35/1.56  thf(sk_A_type, type, sk_A: $i).
% 1.35/1.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.35/1.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.35/1.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.35/1.56  thf(t149_zfmisc_1, conjecture,
% 1.35/1.56    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.56     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.35/1.56         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.35/1.56       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.35/1.56  thf(zf_stmt_0, negated_conjecture,
% 1.35/1.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.56        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.35/1.56            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.35/1.56          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.35/1.56    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.35/1.56  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf(d7_xboole_0, axiom,
% 1.35/1.56    (![A:$i,B:$i]:
% 1.35/1.56     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.35/1.56       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.35/1.56  thf('2', plain,
% 1.35/1.56      (![X2 : $i, X3 : $i]:
% 1.35/1.56         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.35/1.56      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.35/1.56  thf('3', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 1.35/1.56      inference('sup-', [status(thm)], ['1', '2'])).
% 1.35/1.56  thf(commutativity_k3_xboole_0, axiom,
% 1.35/1.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.35/1.56  thf('4', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.56  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 1.35/1.56      inference('demod', [status(thm)], ['3', '4'])).
% 1.35/1.56  thf(d1_enumset1, axiom,
% 1.35/1.56    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.56     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.35/1.56       ( ![E:$i]:
% 1.35/1.56         ( ( r2_hidden @ E @ D ) <=>
% 1.35/1.56           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.35/1.56  thf(zf_stmt_1, axiom,
% 1.35/1.56    (![E:$i,C:$i,B:$i,A:$i]:
% 1.35/1.56     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.35/1.56       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.35/1.56  thf('6', plain,
% 1.35/1.56      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.35/1.56         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 1.35/1.56          | ((X19) = (X20))
% 1.35/1.56          | ((X19) = (X21))
% 1.35/1.56          | ((X19) = (X22)))),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.35/1.56  thf(t3_xboole_0, axiom,
% 1.35/1.56    (![A:$i,B:$i]:
% 1.35/1.56     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.35/1.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.35/1.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.35/1.56            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.35/1.56  thf('7', plain,
% 1.35/1.56      (![X5 : $i, X6 : $i]:
% 1.35/1.56         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 1.35/1.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.35/1.56  thf(t69_enumset1, axiom,
% 1.35/1.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.35/1.56  thf('8', plain, (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 1.35/1.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.35/1.56  thf(t70_enumset1, axiom,
% 1.35/1.56    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.35/1.56  thf('9', plain,
% 1.35/1.56      (![X31 : $i, X32 : $i]:
% 1.35/1.56         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 1.35/1.56      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.35/1.56  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.35/1.56  thf(zf_stmt_3, axiom,
% 1.35/1.56    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.56     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.35/1.56       ( ![E:$i]:
% 1.35/1.56         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.35/1.56  thf('10', plain,
% 1.35/1.56      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.35/1.56         (~ (r2_hidden @ X28 @ X27)
% 1.35/1.56          | ~ (zip_tseitin_0 @ X28 @ X24 @ X25 @ X26)
% 1.35/1.56          | ((X27) != (k1_enumset1 @ X26 @ X25 @ X24)))),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.35/1.56  thf('11', plain,
% 1.35/1.56      (![X24 : $i, X25 : $i, X26 : $i, X28 : $i]:
% 1.35/1.56         (~ (zip_tseitin_0 @ X28 @ X24 @ X25 @ X26)
% 1.35/1.56          | ~ (r2_hidden @ X28 @ (k1_enumset1 @ X26 @ X25 @ X24)))),
% 1.35/1.56      inference('simplify', [status(thm)], ['10'])).
% 1.35/1.56  thf('12', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.56         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.35/1.56          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.35/1.56      inference('sup-', [status(thm)], ['9', '11'])).
% 1.35/1.56  thf('13', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.35/1.56          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.35/1.56      inference('sup-', [status(thm)], ['8', '12'])).
% 1.35/1.56  thf('14', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.35/1.56          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 1.35/1.56      inference('sup-', [status(thm)], ['7', '13'])).
% 1.35/1.56  thf('15', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.35/1.56          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.35/1.56          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.35/1.56          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.35/1.56      inference('sup-', [status(thm)], ['6', '14'])).
% 1.35/1.56  thf('16', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.35/1.56          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.35/1.56      inference('simplify', [status(thm)], ['15'])).
% 1.35/1.56  thf('17', plain,
% 1.35/1.56      (![X5 : $i, X6 : $i]:
% 1.35/1.56         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X6))),
% 1.35/1.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.35/1.56  thf('18', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         ((r2_hidden @ X0 @ X1)
% 1.35/1.56          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.35/1.56          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.35/1.56      inference('sup+', [status(thm)], ['16', '17'])).
% 1.35/1.56  thf('19', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 1.35/1.56      inference('simplify', [status(thm)], ['18'])).
% 1.35/1.56  thf('20', plain,
% 1.35/1.56      (![X2 : $i, X3 : $i]:
% 1.35/1.56         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.35/1.56      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.35/1.56  thf('21', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         ((r2_hidden @ X1 @ X0)
% 1.35/1.56          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 1.35/1.56      inference('sup-', [status(thm)], ['19', '20'])).
% 1.35/1.56  thf(l3_zfmisc_1, axiom,
% 1.35/1.56    (![A:$i,B:$i]:
% 1.35/1.56     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.35/1.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.35/1.56  thf('22', plain,
% 1.35/1.56      (![X52 : $i, X53 : $i]:
% 1.35/1.56         ((r1_tarski @ X52 @ (k1_tarski @ X53)) | ((X52) != (k1_tarski @ X53)))),
% 1.35/1.56      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.35/1.56  thf('23', plain,
% 1.35/1.56      (![X53 : $i]: (r1_tarski @ (k1_tarski @ X53) @ (k1_tarski @ X53))),
% 1.35/1.56      inference('simplify', [status(thm)], ['22'])).
% 1.35/1.56  thf(t28_xboole_1, axiom,
% 1.35/1.56    (![A:$i,B:$i]:
% 1.35/1.56     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.35/1.56  thf('24', plain,
% 1.35/1.56      (![X12 : $i, X13 : $i]:
% 1.35/1.56         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.35/1.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.35/1.56  thf('25', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 1.35/1.56           = (k1_tarski @ X0))),
% 1.35/1.56      inference('sup-', [status(thm)], ['23', '24'])).
% 1.35/1.56  thf('26', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         (((k1_xboole_0) = (k1_tarski @ X0))
% 1.35/1.56          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.35/1.56      inference('sup+', [status(thm)], ['21', '25'])).
% 1.35/1.56  thf('27', plain,
% 1.35/1.56      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('28', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.56  thf('29', plain,
% 1.35/1.56      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.35/1.56      inference('demod', [status(thm)], ['27', '28'])).
% 1.35/1.56  thf('30', plain,
% 1.35/1.56      (![X51 : $i, X52 : $i]:
% 1.35/1.56         (((X52) = (k1_tarski @ X51))
% 1.35/1.56          | ((X52) = (k1_xboole_0))
% 1.35/1.56          | ~ (r1_tarski @ X52 @ (k1_tarski @ X51)))),
% 1.35/1.56      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.35/1.56  thf('31', plain,
% 1.35/1.56      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 1.35/1.56        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_tarski @ sk_D)))),
% 1.35/1.56      inference('sup-', [status(thm)], ['29', '30'])).
% 1.35/1.56  thf('32', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.56  thf('33', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 1.35/1.56      inference('demod', [status(thm)], ['3', '4'])).
% 1.35/1.56  thf(t16_xboole_1, axiom,
% 1.35/1.56    (![A:$i,B:$i,C:$i]:
% 1.35/1.56     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.35/1.56       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.35/1.56  thf('34', plain,
% 1.35/1.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 1.35/1.56           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.35/1.56      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.35/1.56  thf('35', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 1.35/1.56           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 1.35/1.56      inference('sup+', [status(thm)], ['33', '34'])).
% 1.35/1.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.35/1.56  thf('36', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 1.35/1.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.35/1.56  thf('37', plain,
% 1.35/1.56      (![X12 : $i, X13 : $i]:
% 1.35/1.56         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.35/1.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.35/1.56  thf('38', plain,
% 1.35/1.56      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['36', '37'])).
% 1.35/1.57  thf('39', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 1.35/1.57      inference('demod', [status(thm)], ['35', '38'])).
% 1.35/1.57  thf('40', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.57  thf('41', plain,
% 1.35/1.57      (![X2 : $i, X4 : $i]:
% 1.35/1.57         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.35/1.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.35/1.57  thf('42', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 1.35/1.57      inference('sup-', [status(thm)], ['40', '41'])).
% 1.35/1.57  thf('43', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k1_xboole_0) != (k1_xboole_0))
% 1.35/1.57          | (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B))),
% 1.35/1.57      inference('sup-', [status(thm)], ['39', '42'])).
% 1.35/1.57  thf('44', plain,
% 1.35/1.57      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B)),
% 1.35/1.57      inference('simplify', [status(thm)], ['43'])).
% 1.35/1.57  thf('45', plain,
% 1.35/1.57      (![X2 : $i, X3 : $i]:
% 1.35/1.57         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.35/1.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.35/1.57  thf('46', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((k3_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B) = (k1_xboole_0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['44', '45'])).
% 1.35/1.57  thf('47', plain,
% 1.35/1.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.35/1.57         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 1.35/1.57           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.35/1.57  thf('48', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B)) = (k1_xboole_0))),
% 1.35/1.57      inference('demod', [status(thm)], ['46', '47'])).
% 1.35/1.57  thf('49', plain,
% 1.35/1.57      (![X2 : $i, X4 : $i]:
% 1.35/1.57         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.35/1.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.35/1.57  thf('50', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k1_xboole_0) != (k1_xboole_0))
% 1.35/1.57          | (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['48', '49'])).
% 1.35/1.57  thf('51', plain,
% 1.35/1.57      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B))),
% 1.35/1.57      inference('simplify', [status(thm)], ['50'])).
% 1.35/1.57  thf('52', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('53', plain,
% 1.35/1.57      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.35/1.57         (~ (r2_hidden @ X7 @ X5)
% 1.35/1.57          | ~ (r2_hidden @ X7 @ X8)
% 1.35/1.57          | ~ (r1_xboole_0 @ X5 @ X8))),
% 1.35/1.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.35/1.57  thf('54', plain,
% 1.35/1.57      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['52', '53'])).
% 1.35/1.57  thf('55', plain,
% 1.35/1.57      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ X0 @ sk_B))),
% 1.35/1.57      inference('sup-', [status(thm)], ['51', '54'])).
% 1.35/1.57  thf('56', plain,
% 1.35/1.57      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['32', '55'])).
% 1.35/1.57  thf('57', plain,
% 1.35/1.57      ((~ (r2_hidden @ sk_D @ (k1_tarski @ sk_D))
% 1.35/1.57        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['31', '56'])).
% 1.35/1.57  thf('58', plain,
% 1.35/1.57      ((((k1_xboole_0) = (k1_tarski @ sk_D))
% 1.35/1.57        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['26', '57'])).
% 1.35/1.57  thf('59', plain,
% 1.35/1.57      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 1.35/1.57        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_tarski @ sk_D)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['29', '30'])).
% 1.35/1.57  thf('60', plain,
% 1.35/1.57      ((((k1_tarski @ sk_D) != (k1_xboole_0))
% 1.35/1.57        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.35/1.57      inference('eq_fact', [status(thm)], ['59'])).
% 1.35/1.57  thf('61', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.35/1.57      inference('clc', [status(thm)], ['58', '60'])).
% 1.35/1.57  thf('62', plain,
% 1.35/1.57      (![X2 : $i, X4 : $i]:
% 1.35/1.57         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.35/1.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.35/1.57  thf('63', plain,
% 1.35/1.57      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 1.35/1.57      inference('sup-', [status(thm)], ['61', '62'])).
% 1.35/1.57  thf('64', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.35/1.57      inference('simplify', [status(thm)], ['63'])).
% 1.35/1.57  thf(t78_xboole_1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i]:
% 1.35/1.57     ( ( r1_xboole_0 @ A @ B ) =>
% 1.35/1.57       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.35/1.57         ( k3_xboole_0 @ A @ C ) ) ))).
% 1.35/1.57  thf('65', plain,
% 1.35/1.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.35/1.57         (~ (r1_xboole_0 @ X15 @ X16)
% 1.35/1.57          | ((k3_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 1.35/1.57              = (k3_xboole_0 @ X15 @ X17)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t78_xboole_1])).
% 1.35/1.57  thf('66', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 1.35/1.57           = (k3_xboole_0 @ sk_B @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.57  thf('67', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 1.35/1.57      inference('sup-', [status(thm)], ['40', '41'])).
% 1.35/1.57  thf('68', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 1.35/1.57          | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 1.35/1.57      inference('sup-', [status(thm)], ['66', '67'])).
% 1.35/1.57  thf('69', plain,
% 1.35/1.57      ((((k1_xboole_0) != (k1_xboole_0))
% 1.35/1.57        | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B))),
% 1.35/1.57      inference('sup-', [status(thm)], ['5', '68'])).
% 1.35/1.57  thf('70', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.35/1.57      inference('simplify', [status(thm)], ['69'])).
% 1.35/1.57  thf('71', plain, ($false), inference('demod', [status(thm)], ['0', '70'])).
% 1.35/1.57  
% 1.35/1.57  % SZS output end Refutation
% 1.35/1.57  
% 1.35/1.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
