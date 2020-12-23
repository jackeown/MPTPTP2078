%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ypEHLjjUXl

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:34 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 317 expanded)
%              Number of leaves         :   30 ( 110 expanded)
%              Depth                    :   17
%              Number of atoms          : 1171 (2666 expanded)
%              Number of equality atoms :  113 ( 263 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( X24 = X25 )
      | ( X24 = X26 )
      | ( X24 = X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( X24 = X25 )
      | ( X24 = X26 )
      | ( X24 = X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('9',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( r2_hidden @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B_1 ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
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

thf('14',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X32 )
      | ~ ( zip_tseitin_0 @ X33 @ X29 @ X30 @ X31 )
      | ( X32
       != ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X29: $i,X30: $i,X31: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X29 @ X30 @ X31 )
      | ~ ( r2_hidden @ X33 @ ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B_1 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,
    ( ( ( sk_B @ ( k1_tarski @ sk_A ) )
      = sk_B_1 )
    | ( ( sk_B @ ( k1_tarski @ sk_A ) )
      = sk_B_1 )
    | ( ( sk_B @ ( k1_tarski @ sk_A ) )
      = sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','18'])).

thf('20',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_tarski @ sk_A ) )
      = sk_B_1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A @ sk_A @ sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A @ sk_A @ sk_A ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( sk_B_1 = sk_A )
    | ( sk_B_1 = sk_A )
    | ( sk_B_1 = sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_B_1 = sk_A ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('29',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('31',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 )
      | ( r2_hidden @ X28 @ X32 )
      | ( X32
       != ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X28 @ ( k1_enumset1 @ X31 @ X30 @ X29 ) )
      | ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X24 != X23 )
      | ~ ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ~ ( zip_tseitin_0 @ X23 @ X25 @ X26 @ X23 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('38',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('39',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( X24 = X25 )
      | ( X24 = X26 )
      | ( X24 = X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('41',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('42',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('57',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('61',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('63',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('69',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('74',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['66','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['59','81'])).

thf('83',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('84',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('85',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_xboole_0 @ X20 @ X22 )
      | ( ( k4_xboole_0 @ X20 @ X22 )
       != X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != X1 )
      | ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('93',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['82','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','101'])).

thf('103',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['29','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','96'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','96'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','97'])).

thf('112',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','115'])).

thf('117',plain,(
    $false ),
    inference('sup-',[status(thm)],['103','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ypEHLjjUXl
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:33:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.00/1.22  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.00/1.22  % Solved by: fo/fo7.sh
% 1.00/1.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.22  % done 1732 iterations in 0.766s
% 1.00/1.22  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.00/1.22  % SZS output start Refutation
% 1.00/1.22  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.00/1.22  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.22  thf(sk_B_type, type, sk_B: $i > $i).
% 1.00/1.22  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.00/1.22  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.00/1.22  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.00/1.22  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.00/1.22  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.00/1.22  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.00/1.22  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.00/1.22  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.00/1.22  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.00/1.22  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.00/1.22  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.00/1.22  thf(d1_enumset1, axiom,
% 1.00/1.22    (![A:$i,B:$i,C:$i,D:$i]:
% 1.00/1.22     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.00/1.22       ( ![E:$i]:
% 1.00/1.22         ( ( r2_hidden @ E @ D ) <=>
% 1.00/1.22           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.00/1.22  thf(zf_stmt_0, axiom,
% 1.00/1.22    (![E:$i,C:$i,B:$i,A:$i]:
% 1.00/1.22     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.00/1.22       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.00/1.22  thf('0', plain,
% 1.00/1.22      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.00/1.22         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 1.00/1.22          | ((X24) = (X25))
% 1.00/1.22          | ((X24) = (X26))
% 1.00/1.22          | ((X24) = (X27)))),
% 1.00/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.22  thf('1', plain,
% 1.00/1.22      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.00/1.22         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 1.00/1.22          | ((X24) = (X25))
% 1.00/1.22          | ((X24) = (X26))
% 1.00/1.22          | ((X24) = (X27)))),
% 1.00/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.22  thf(t18_zfmisc_1, conjecture,
% 1.00/1.22    (![A:$i,B:$i]:
% 1.00/1.22     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.00/1.22         ( k1_tarski @ A ) ) =>
% 1.00/1.22       ( ( A ) = ( B ) ) ))).
% 1.00/1.22  thf(zf_stmt_1, negated_conjecture,
% 1.00/1.22    (~( ![A:$i,B:$i]:
% 1.00/1.22        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.00/1.22            ( k1_tarski @ A ) ) =>
% 1.00/1.22          ( ( A ) = ( B ) ) ) )),
% 1.00/1.22    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 1.00/1.22  thf('2', plain,
% 1.00/1.22      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 1.00/1.22         = (k1_tarski @ sk_A))),
% 1.00/1.22      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.00/1.22  thf(commutativity_k3_xboole_0, axiom,
% 1.00/1.22    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.00/1.22  thf('3', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.00/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.00/1.22  thf('4', plain,
% 1.00/1.22      (((k3_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 1.00/1.22         = (k1_tarski @ sk_A))),
% 1.00/1.22      inference('demod', [status(thm)], ['2', '3'])).
% 1.00/1.22  thf(t22_xboole_1, axiom,
% 1.00/1.22    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.00/1.22  thf('5', plain,
% 1.00/1.22      (![X14 : $i, X15 : $i]:
% 1.00/1.22         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)) = (X14))),
% 1.00/1.22      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.00/1.22  thf('6', plain,
% 1.00/1.22      (((k2_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 1.00/1.22         = (k1_tarski @ sk_B_1))),
% 1.00/1.22      inference('sup+', [status(thm)], ['4', '5'])).
% 1.00/1.22  thf(t7_xboole_0, axiom,
% 1.00/1.22    (![A:$i]:
% 1.00/1.22     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.00/1.22          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.00/1.22  thf('7', plain,
% 1.00/1.22      (![X13 : $i]:
% 1.00/1.22         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 1.00/1.22      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.00/1.22  thf(d3_xboole_0, axiom,
% 1.00/1.22    (![A:$i,B:$i,C:$i]:
% 1.00/1.22     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.00/1.22       ( ![D:$i]:
% 1.00/1.22         ( ( r2_hidden @ D @ C ) <=>
% 1.00/1.22           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.00/1.22  thf('8', plain,
% 1.00/1.22      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.00/1.22         (~ (r2_hidden @ X2 @ X3)
% 1.00/1.22          | (r2_hidden @ X2 @ X4)
% 1.00/1.22          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 1.00/1.22      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.00/1.22  thf('9', plain,
% 1.00/1.22      (![X2 : $i, X3 : $i, X5 : $i]:
% 1.00/1.22         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 1.00/1.22      inference('simplify', [status(thm)], ['8'])).
% 1.00/1.22  thf('10', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         (((X0) = (k1_xboole_0))
% 1.00/1.22          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 1.00/1.22      inference('sup-', [status(thm)], ['7', '9'])).
% 1.00/1.22  thf('11', plain,
% 1.00/1.22      (((r2_hidden @ (sk_B @ (k1_tarski @ sk_A)) @ (k1_tarski @ sk_B_1))
% 1.00/1.22        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 1.00/1.22      inference('sup+', [status(thm)], ['6', '10'])).
% 1.00/1.22  thf(t69_enumset1, axiom,
% 1.00/1.22    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.00/1.22  thf('12', plain,
% 1.00/1.22      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 1.00/1.22      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.00/1.22  thf(t70_enumset1, axiom,
% 1.00/1.22    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.00/1.22  thf('13', plain,
% 1.00/1.22      (![X36 : $i, X37 : $i]:
% 1.00/1.22         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 1.00/1.22      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.00/1.22  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.00/1.22  thf(zf_stmt_3, axiom,
% 1.00/1.22    (![A:$i,B:$i,C:$i,D:$i]:
% 1.00/1.22     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.00/1.22       ( ![E:$i]:
% 1.00/1.22         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.00/1.22  thf('14', plain,
% 1.00/1.22      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.00/1.22         (~ (r2_hidden @ X33 @ X32)
% 1.00/1.22          | ~ (zip_tseitin_0 @ X33 @ X29 @ X30 @ X31)
% 1.00/1.22          | ((X32) != (k1_enumset1 @ X31 @ X30 @ X29)))),
% 1.00/1.22      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.00/1.22  thf('15', plain,
% 1.00/1.22      (![X29 : $i, X30 : $i, X31 : $i, X33 : $i]:
% 1.00/1.22         (~ (zip_tseitin_0 @ X33 @ X29 @ X30 @ X31)
% 1.00/1.22          | ~ (r2_hidden @ X33 @ (k1_enumset1 @ X31 @ X30 @ X29)))),
% 1.00/1.22      inference('simplify', [status(thm)], ['14'])).
% 1.00/1.22  thf('16', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.22         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.00/1.22          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.00/1.22      inference('sup-', [status(thm)], ['13', '15'])).
% 1.00/1.22  thf('17', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.00/1.22          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.00/1.22      inference('sup-', [status(thm)], ['12', '16'])).
% 1.00/1.22  thf('18', plain,
% 1.00/1.22      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 1.00/1.22        | ~ (zip_tseitin_0 @ (sk_B @ (k1_tarski @ sk_A)) @ sk_B_1 @ sk_B_1 @ 
% 1.00/1.22             sk_B_1))),
% 1.00/1.22      inference('sup-', [status(thm)], ['11', '17'])).
% 1.00/1.22  thf('19', plain,
% 1.00/1.22      ((((sk_B @ (k1_tarski @ sk_A)) = (sk_B_1))
% 1.00/1.22        | ((sk_B @ (k1_tarski @ sk_A)) = (sk_B_1))
% 1.00/1.22        | ((sk_B @ (k1_tarski @ sk_A)) = (sk_B_1))
% 1.00/1.22        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 1.00/1.22      inference('sup-', [status(thm)], ['1', '18'])).
% 1.00/1.22  thf('20', plain,
% 1.00/1.22      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 1.00/1.22        | ((sk_B @ (k1_tarski @ sk_A)) = (sk_B_1)))),
% 1.00/1.22      inference('simplify', [status(thm)], ['19'])).
% 1.00/1.22  thf('21', plain,
% 1.00/1.22      (![X13 : $i]:
% 1.00/1.22         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 1.00/1.22      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.00/1.22  thf('22', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.00/1.22          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.00/1.22      inference('sup-', [status(thm)], ['12', '16'])).
% 1.00/1.22  thf('23', plain,
% 1.00/1.22      (![X0 : $i]:
% 1.00/1.22         (((k1_tarski @ X0) = (k1_xboole_0))
% 1.00/1.22          | ~ (zip_tseitin_0 @ (sk_B @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 1.00/1.22      inference('sup-', [status(thm)], ['21', '22'])).
% 1.00/1.22  thf('24', plain,
% 1.00/1.22      ((~ (zip_tseitin_0 @ sk_B_1 @ sk_A @ sk_A @ sk_A)
% 1.00/1.22        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 1.00/1.22        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 1.00/1.22      inference('sup-', [status(thm)], ['20', '23'])).
% 1.00/1.22  thf('25', plain,
% 1.00/1.22      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 1.00/1.22        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A @ sk_A @ sk_A))),
% 1.00/1.22      inference('simplify', [status(thm)], ['24'])).
% 1.00/1.22  thf('26', plain,
% 1.00/1.22      ((((sk_B_1) = (sk_A))
% 1.00/1.22        | ((sk_B_1) = (sk_A))
% 1.00/1.22        | ((sk_B_1) = (sk_A))
% 1.00/1.22        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 1.00/1.22      inference('sup-', [status(thm)], ['0', '25'])).
% 1.00/1.22  thf('27', plain,
% 1.00/1.22      ((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_B_1) = (sk_A)))),
% 1.00/1.22      inference('simplify', [status(thm)], ['26'])).
% 1.00/1.22  thf('28', plain, (((sk_A) != (sk_B_1))),
% 1.00/1.22      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.00/1.22  thf('29', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 1.00/1.22      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 1.00/1.22  thf('30', plain,
% 1.00/1.22      (![X36 : $i, X37 : $i]:
% 1.00/1.22         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 1.00/1.22      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.00/1.22  thf('31', plain,
% 1.00/1.22      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.00/1.22         ((zip_tseitin_0 @ X28 @ X29 @ X30 @ X31)
% 1.00/1.22          | (r2_hidden @ X28 @ X32)
% 1.00/1.22          | ((X32) != (k1_enumset1 @ X31 @ X30 @ X29)))),
% 1.00/1.22      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.00/1.22  thf('32', plain,
% 1.00/1.22      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.00/1.22         ((r2_hidden @ X28 @ (k1_enumset1 @ X31 @ X30 @ X29))
% 1.00/1.22          | (zip_tseitin_0 @ X28 @ X29 @ X30 @ X31))),
% 1.00/1.22      inference('simplify', [status(thm)], ['31'])).
% 1.00/1.22  thf('33', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.22         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.00/1.22          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.00/1.22      inference('sup+', [status(thm)], ['30', '32'])).
% 1.00/1.22  thf('34', plain,
% 1.00/1.22      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.00/1.22         (((X24) != (X23)) | ~ (zip_tseitin_0 @ X24 @ X25 @ X26 @ X23))),
% 1.00/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.22  thf('35', plain,
% 1.00/1.22      (![X23 : $i, X25 : $i, X26 : $i]:
% 1.00/1.22         ~ (zip_tseitin_0 @ X23 @ X25 @ X26 @ X23)),
% 1.00/1.22      inference('simplify', [status(thm)], ['34'])).
% 1.00/1.22  thf('36', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.00/1.22      inference('sup-', [status(thm)], ['33', '35'])).
% 1.00/1.22  thf('37', plain,
% 1.00/1.22      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 1.00/1.22      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.00/1.22  thf(idempotence_k3_xboole_0, axiom,
% 1.00/1.22    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.00/1.22  thf('38', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 1.00/1.22      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.00/1.22  thf('39', plain,
% 1.00/1.22      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.00/1.22         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 1.00/1.22          | ((X24) = (X25))
% 1.00/1.22          | ((X24) = (X26))
% 1.00/1.22          | ((X24) = (X27)))),
% 1.00/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.22  thf('40', plain,
% 1.00/1.22      (![X14 : $i, X15 : $i]:
% 1.00/1.22         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)) = (X14))),
% 1.00/1.22      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.00/1.22  thf(t4_xboole_0, axiom,
% 1.00/1.22    (![A:$i,B:$i]:
% 1.00/1.22     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.00/1.22            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.00/1.22       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.00/1.22            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.00/1.22  thf('41', plain,
% 1.00/1.22      (![X9 : $i, X10 : $i]:
% 1.00/1.22         ((r1_xboole_0 @ X9 @ X10)
% 1.00/1.22          | (r2_hidden @ (sk_C @ X10 @ X9) @ (k3_xboole_0 @ X9 @ X10)))),
% 1.00/1.22      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.00/1.22  thf('42', plain,
% 1.00/1.22      (![X2 : $i, X3 : $i, X5 : $i]:
% 1.00/1.22         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 1.00/1.22      inference('simplify', [status(thm)], ['8'])).
% 1.00/1.22  thf('43', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.22         ((r1_xboole_0 @ X1 @ X0)
% 1.00/1.22          | (r2_hidden @ (sk_C @ X0 @ X1) @ 
% 1.00/1.22             (k2_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.00/1.22      inference('sup-', [status(thm)], ['41', '42'])).
% 1.00/1.22  thf('44', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         ((r2_hidden @ (sk_C @ X1 @ X0) @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.00/1.22      inference('sup+', [status(thm)], ['40', '43'])).
% 1.00/1.22  thf('45', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.00/1.22          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.00/1.22      inference('sup-', [status(thm)], ['12', '16'])).
% 1.00/1.22  thf('46', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.00/1.22          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 1.00/1.22      inference('sup-', [status(thm)], ['44', '45'])).
% 1.00/1.22  thf('47', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.00/1.22          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.00/1.22          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.00/1.22          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.00/1.22      inference('sup-', [status(thm)], ['39', '46'])).
% 1.00/1.22  thf('48', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.00/1.22          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.00/1.22      inference('simplify', [status(thm)], ['47'])).
% 1.00/1.22  thf('49', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.00/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.00/1.22  thf('50', plain,
% 1.00/1.22      (![X14 : $i, X15 : $i]:
% 1.00/1.22         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)) = (X14))),
% 1.00/1.22      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.00/1.22  thf('51', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 1.00/1.22      inference('sup+', [status(thm)], ['49', '50'])).
% 1.00/1.22  thf('52', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.22         ((r1_xboole_0 @ X1 @ X0)
% 1.00/1.22          | (r2_hidden @ (sk_C @ X0 @ X1) @ 
% 1.00/1.22             (k2_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.00/1.22      inference('sup-', [status(thm)], ['41', '42'])).
% 1.00/1.22  thf('53', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         ((r2_hidden @ (sk_C @ X0 @ X1) @ X0) | (r1_xboole_0 @ X1 @ X0))),
% 1.00/1.22      inference('sup+', [status(thm)], ['51', '52'])).
% 1.00/1.22  thf('54', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         ((r2_hidden @ X0 @ X1)
% 1.00/1.22          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.00/1.22          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.00/1.22      inference('sup+', [status(thm)], ['48', '53'])).
% 1.00/1.22  thf('55', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 1.00/1.22      inference('simplify', [status(thm)], ['54'])).
% 1.00/1.22  thf('56', plain,
% 1.00/1.22      (![X13 : $i]:
% 1.00/1.22         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 1.00/1.22      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.00/1.22  thf('57', plain,
% 1.00/1.22      (![X9 : $i, X11 : $i, X12 : $i]:
% 1.00/1.22         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 1.00/1.22          | ~ (r1_xboole_0 @ X9 @ X12))),
% 1.00/1.22      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.00/1.22  thf('58', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.00/1.22      inference('sup-', [status(thm)], ['56', '57'])).
% 1.00/1.22  thf('59', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         ((r2_hidden @ X1 @ X0)
% 1.00/1.22          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 1.00/1.22      inference('sup-', [status(thm)], ['55', '58'])).
% 1.00/1.22  thf('60', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.00/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.00/1.22  thf(t47_xboole_1, axiom,
% 1.00/1.22    (![A:$i,B:$i]:
% 1.00/1.22     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.00/1.22  thf('61', plain,
% 1.00/1.22      (![X16 : $i, X17 : $i]:
% 1.00/1.22         ((k4_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17))
% 1.00/1.22           = (k4_xboole_0 @ X16 @ X17))),
% 1.00/1.22      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.00/1.22  thf('62', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.00/1.22           = (k4_xboole_0 @ X0 @ X1))),
% 1.00/1.22      inference('sup+', [status(thm)], ['60', '61'])).
% 1.00/1.22  thf(t48_xboole_1, axiom,
% 1.00/1.22    (![A:$i,B:$i]:
% 1.00/1.22     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.00/1.22  thf('63', plain,
% 1.00/1.22      (![X18 : $i, X19 : $i]:
% 1.00/1.22         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.00/1.22           = (k3_xboole_0 @ X18 @ X19))),
% 1.00/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.22  thf('64', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.00/1.22           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.00/1.22      inference('sup+', [status(thm)], ['62', '63'])).
% 1.00/1.22  thf('65', plain,
% 1.00/1.22      (![X18 : $i, X19 : $i]:
% 1.00/1.22         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.00/1.22           = (k3_xboole_0 @ X18 @ X19))),
% 1.00/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.22  thf('66', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         ((k3_xboole_0 @ X1 @ X0)
% 1.00/1.22           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.00/1.22      inference('demod', [status(thm)], ['64', '65'])).
% 1.00/1.22  thf('67', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.00/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.00/1.22  thf('68', plain,
% 1.00/1.22      (![X16 : $i, X17 : $i]:
% 1.00/1.22         ((k4_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17))
% 1.00/1.22           = (k4_xboole_0 @ X16 @ X17))),
% 1.00/1.22      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.00/1.22  thf('69', plain,
% 1.00/1.22      (![X18 : $i, X19 : $i]:
% 1.00/1.22         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.00/1.22           = (k3_xboole_0 @ X18 @ X19))),
% 1.00/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.22  thf('70', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.00/1.22           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.00/1.22      inference('sup+', [status(thm)], ['68', '69'])).
% 1.00/1.22  thf('71', plain,
% 1.00/1.22      (![X18 : $i, X19 : $i]:
% 1.00/1.22         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.00/1.22           = (k3_xboole_0 @ X18 @ X19))),
% 1.00/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.22  thf('72', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         ((k3_xboole_0 @ X1 @ X0)
% 1.00/1.22           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.00/1.22      inference('demod', [status(thm)], ['70', '71'])).
% 1.00/1.22  thf('73', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.00/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.00/1.22  thf('74', plain,
% 1.00/1.22      (![X9 : $i, X11 : $i, X12 : $i]:
% 1.00/1.22         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 1.00/1.22          | ~ (r1_xboole_0 @ X9 @ X12))),
% 1.00/1.22      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.00/1.22  thf('75', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.22         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.00/1.22          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.00/1.22      inference('sup-', [status(thm)], ['73', '74'])).
% 1.00/1.22  thf('76', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.22         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.00/1.22          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.00/1.22      inference('sup-', [status(thm)], ['72', '75'])).
% 1.00/1.22  thf('77', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.22         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.00/1.22          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 1.00/1.22      inference('sup-', [status(thm)], ['67', '76'])).
% 1.00/1.22  thf('78', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.22         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.00/1.22          | ~ (r1_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1) @ 
% 1.00/1.22               (k3_xboole_0 @ X0 @ X1)))),
% 1.00/1.22      inference('sup-', [status(thm)], ['66', '77'])).
% 1.00/1.22  thf('79', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.00/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.00/1.22  thf('80', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         ((k3_xboole_0 @ X1 @ X0)
% 1.00/1.22           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.00/1.22      inference('demod', [status(thm)], ['64', '65'])).
% 1.00/1.22  thf('81', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.22         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.00/1.22          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 1.00/1.22      inference('demod', [status(thm)], ['78', '79', '80'])).
% 1.00/1.22  thf('82', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.22         (~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1)) @ k1_xboole_0)
% 1.00/1.22          | (r2_hidden @ X1 @ X0)
% 1.00/1.22          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 1.00/1.22      inference('sup-', [status(thm)], ['59', '81'])).
% 1.00/1.22  thf('83', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 1.00/1.22      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.00/1.22  thf('84', plain,
% 1.00/1.22      (![X18 : $i, X19 : $i]:
% 1.00/1.22         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.00/1.22           = (k3_xboole_0 @ X18 @ X19))),
% 1.00/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.22  thf(t83_xboole_1, axiom,
% 1.00/1.22    (![A:$i,B:$i]:
% 1.00/1.22     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.00/1.22  thf('85', plain,
% 1.00/1.22      (![X20 : $i, X22 : $i]:
% 1.00/1.22         ((r1_xboole_0 @ X20 @ X22) | ((k4_xboole_0 @ X20 @ X22) != (X20)))),
% 1.00/1.22      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.00/1.22  thf('86', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         (((k3_xboole_0 @ X1 @ X0) != (X1))
% 1.00/1.22          | (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.00/1.22      inference('sup-', [status(thm)], ['84', '85'])).
% 1.00/1.22  thf('87', plain,
% 1.00/1.22      (![X0 : $i]:
% 1.00/1.22         (((X0) != (X0)) | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 1.00/1.22      inference('sup-', [status(thm)], ['83', '86'])).
% 1.00/1.22  thf('88', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))),
% 1.00/1.22      inference('simplify', [status(thm)], ['87'])).
% 1.00/1.22  thf('89', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))),
% 1.00/1.22      inference('simplify', [status(thm)], ['87'])).
% 1.00/1.22  thf('90', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.00/1.22      inference('sup-', [status(thm)], ['56', '57'])).
% 1.00/1.22  thf('91', plain,
% 1.00/1.22      (![X0 : $i]:
% 1.00/1.22         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 1.00/1.22      inference('sup-', [status(thm)], ['89', '90'])).
% 1.00/1.22  thf('92', plain,
% 1.00/1.22      (![X18 : $i, X19 : $i]:
% 1.00/1.22         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.00/1.22           = (k3_xboole_0 @ X18 @ X19))),
% 1.00/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.22  thf('93', plain,
% 1.00/1.22      (![X18 : $i, X19 : $i]:
% 1.00/1.22         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.00/1.22           = (k3_xboole_0 @ X18 @ X19))),
% 1.00/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.22  thf('94', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.00/1.22           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.00/1.22      inference('sup+', [status(thm)], ['92', '93'])).
% 1.00/1.22  thf('95', plain,
% 1.00/1.22      (![X16 : $i, X17 : $i]:
% 1.00/1.22         ((k4_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17))
% 1.00/1.22           = (k4_xboole_0 @ X16 @ X17))),
% 1.00/1.22      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.00/1.22  thf('96', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.00/1.22           = (k4_xboole_0 @ X1 @ X0))),
% 1.00/1.22      inference('sup+', [status(thm)], ['94', '95'])).
% 1.00/1.22  thf('97', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.00/1.22      inference('demod', [status(thm)], ['91', '96'])).
% 1.00/1.22  thf('98', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.00/1.22      inference('demod', [status(thm)], ['88', '97'])).
% 1.00/1.22  thf('99', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.22         ((r2_hidden @ X1 @ X0)
% 1.00/1.22          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 1.00/1.22      inference('demod', [status(thm)], ['82', '98'])).
% 1.00/1.22  thf('100', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.00/1.22          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.00/1.22      inference('sup-', [status(thm)], ['38', '99'])).
% 1.00/1.22  thf('101', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 1.00/1.22          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.00/1.22      inference('sup-', [status(thm)], ['37', '100'])).
% 1.00/1.22  thf('102', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.00/1.22      inference('sup-', [status(thm)], ['36', '101'])).
% 1.00/1.22  thf('103', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 1.00/1.22      inference('sup+', [status(thm)], ['29', '102'])).
% 1.00/1.22  thf('104', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.00/1.22      inference('demod', [status(thm)], ['91', '96'])).
% 1.00/1.22  thf('105', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.00/1.22           = (k4_xboole_0 @ X1 @ X0))),
% 1.00/1.22      inference('sup+', [status(thm)], ['94', '95'])).
% 1.00/1.22  thf('106', plain,
% 1.00/1.22      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.00/1.22      inference('sup+', [status(thm)], ['104', '105'])).
% 1.00/1.22  thf('107', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.00/1.22      inference('demod', [status(thm)], ['91', '96'])).
% 1.00/1.22  thf('108', plain,
% 1.00/1.22      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.00/1.22      inference('demod', [status(thm)], ['106', '107'])).
% 1.00/1.22  thf('109', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.22         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.00/1.22          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.00/1.22      inference('sup-', [status(thm)], ['73', '74'])).
% 1.00/1.22  thf('110', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 1.00/1.22      inference('sup-', [status(thm)], ['108', '109'])).
% 1.00/1.22  thf('111', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.00/1.22      inference('demod', [status(thm)], ['88', '97'])).
% 1.00/1.22  thf('112', plain,
% 1.00/1.22      (![X9 : $i, X10 : $i]:
% 1.00/1.22         ((r1_xboole_0 @ X9 @ X10)
% 1.00/1.22          | (r2_hidden @ (sk_C @ X10 @ X9) @ (k3_xboole_0 @ X9 @ X10)))),
% 1.00/1.22      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.00/1.22  thf('113', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.22         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.00/1.22          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.00/1.22      inference('sup-', [status(thm)], ['73', '74'])).
% 1.00/1.22  thf('114', plain,
% 1.00/1.22      (![X0 : $i, X1 : $i]:
% 1.00/1.22         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.00/1.22      inference('sup-', [status(thm)], ['112', '113'])).
% 1.00/1.22  thf('115', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.00/1.22      inference('sup-', [status(thm)], ['111', '114'])).
% 1.00/1.22  thf('116', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.00/1.22      inference('demod', [status(thm)], ['110', '115'])).
% 1.00/1.22  thf('117', plain, ($false), inference('sup-', [status(thm)], ['103', '116'])).
% 1.00/1.22  
% 1.00/1.22  % SZS output end Refutation
% 1.00/1.22  
% 1.00/1.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
