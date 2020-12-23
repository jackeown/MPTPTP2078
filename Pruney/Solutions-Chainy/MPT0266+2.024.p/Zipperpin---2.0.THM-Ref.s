%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dbPfJiXMYf

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:47 EST 2020

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 136 expanded)
%              Number of leaves         :   25 (  51 expanded)
%              Depth                    :   18
%              Number of atoms          :  928 (1375 expanded)
%              Number of equality atoms :   39 (  66 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( X21 = X22 )
      | ( X21 = X23 )
      | ( X21 = X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k1_enumset1 @ X52 @ X52 @ X53 )
      = ( k2_tarski @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X51: $i] :
      ( ( k2_tarski @ X51 @ X51 )
      = ( k1_tarski @ X51 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ~ ( zip_tseitin_0 @ X30 @ X26 @ X27 @ X28 )
      | ( X29
       != ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X26: $i,X27: $i,X28: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X26 @ X27 @ X28 )
      | ~ ( r2_hidden @ X30 @ ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t63_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_zfmisc_1])).

thf('14',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X7 ) )
      | ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k5_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('36',plain,(
    r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('38',plain,(
    r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('43',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ sk_C_1 )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['15','57'])).

thf('59',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k1_enumset1 @ X52 @ X52 @ X53 )
      = ( k2_tarski @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('60',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 )
      | ( r2_hidden @ X25 @ X29 )
      | ( X29
       != ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('61',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X25 @ ( k1_enumset1 @ X28 @ X27 @ X26 ) )
      | ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','61'])).

thf('63',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X21 != X20 )
      | ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ~ ( zip_tseitin_0 @ X20 @ X22 @ X23 @ X20 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,(
    ! [X51: $i] :
      ( ( k2_tarski @ X51 @ X51 )
      = ( k1_tarski @ X51 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['68','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dbPfJiXMYf
% 0.16/0.37  % Computer   : n021.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 18:29:50 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.73/0.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.73/0.94  % Solved by: fo/fo7.sh
% 0.73/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.73/0.94  % done 877 iterations in 0.461s
% 0.73/0.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.73/0.94  % SZS output start Refutation
% 0.73/0.94  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.73/0.94  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.73/0.94  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.73/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.73/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.73/0.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.73/0.94  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.73/0.94  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.73/0.94  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.73/0.94  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.73/0.94  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.73/0.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.73/0.94  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.73/0.94  thf(d1_enumset1, axiom,
% 0.73/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.73/0.94     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.73/0.94       ( ![E:$i]:
% 0.73/0.94         ( ( r2_hidden @ E @ D ) <=>
% 0.73/0.94           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.73/0.94  thf(zf_stmt_0, axiom,
% 0.73/0.94    (![E:$i,C:$i,B:$i,A:$i]:
% 0.73/0.94     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.73/0.94       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.73/0.94  thf('0', plain,
% 0.73/0.94      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.73/0.94         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 0.73/0.94          | ((X21) = (X22))
% 0.73/0.94          | ((X21) = (X23))
% 0.73/0.94          | ((X21) = (X24)))),
% 0.73/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.94  thf(t3_xboole_0, axiom,
% 0.73/0.94    (![A:$i,B:$i]:
% 0.73/0.94     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.73/0.94            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.73/0.94       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.73/0.94            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.73/0.94  thf('1', plain,
% 0.73/0.94      (![X8 : $i, X9 : $i]:
% 0.73/0.94         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.73/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.73/0.94  thf(t70_enumset1, axiom,
% 0.73/0.94    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.73/0.94  thf('2', plain,
% 0.73/0.94      (![X52 : $i, X53 : $i]:
% 0.73/0.94         ((k1_enumset1 @ X52 @ X52 @ X53) = (k2_tarski @ X52 @ X53))),
% 0.73/0.94      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.73/0.94  thf(t69_enumset1, axiom,
% 0.73/0.94    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.73/0.94  thf('3', plain, (![X51 : $i]: ((k2_tarski @ X51 @ X51) = (k1_tarski @ X51))),
% 0.73/0.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.73/0.94  thf('4', plain,
% 0.73/0.94      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.73/0.94      inference('sup+', [status(thm)], ['2', '3'])).
% 0.73/0.94  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.73/0.94  thf(zf_stmt_2, axiom,
% 0.73/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.73/0.94     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.73/0.94       ( ![E:$i]:
% 0.73/0.94         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.73/0.94  thf('5', plain,
% 0.73/0.94      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.73/0.94         (~ (r2_hidden @ X30 @ X29)
% 0.73/0.94          | ~ (zip_tseitin_0 @ X30 @ X26 @ X27 @ X28)
% 0.73/0.94          | ((X29) != (k1_enumset1 @ X28 @ X27 @ X26)))),
% 0.73/0.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.73/0.94  thf('6', plain,
% 0.73/0.94      (![X26 : $i, X27 : $i, X28 : $i, X30 : $i]:
% 0.73/0.94         (~ (zip_tseitin_0 @ X30 @ X26 @ X27 @ X28)
% 0.73/0.94          | ~ (r2_hidden @ X30 @ (k1_enumset1 @ X28 @ X27 @ X26)))),
% 0.73/0.94      inference('simplify', [status(thm)], ['5'])).
% 0.73/0.94  thf('7', plain,
% 0.73/0.94      (![X0 : $i, X1 : $i]:
% 0.73/0.94         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.73/0.94          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.73/0.94      inference('sup-', [status(thm)], ['4', '6'])).
% 0.73/0.94  thf('8', plain,
% 0.73/0.94      (![X0 : $i, X1 : $i]:
% 0.73/0.94         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.73/0.94          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.73/0.94      inference('sup-', [status(thm)], ['1', '7'])).
% 0.73/0.94  thf('9', plain,
% 0.73/0.94      (![X0 : $i, X1 : $i]:
% 0.73/0.94         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.73/0.94          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.73/0.94          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.73/0.94          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.73/0.94      inference('sup-', [status(thm)], ['0', '8'])).
% 0.73/0.94  thf('10', plain,
% 0.73/0.94      (![X0 : $i, X1 : $i]:
% 0.73/0.94         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.73/0.94          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.73/0.94      inference('simplify', [status(thm)], ['9'])).
% 0.73/0.94  thf('11', plain,
% 0.73/0.94      (![X8 : $i, X9 : $i]:
% 0.73/0.94         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 0.73/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.73/0.94  thf('12', plain,
% 0.73/0.94      (![X0 : $i, X1 : $i]:
% 0.73/0.94         ((r2_hidden @ X0 @ X1)
% 0.73/0.94          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.73/0.94          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.73/0.94      inference('sup+', [status(thm)], ['10', '11'])).
% 0.73/0.94  thf('13', plain,
% 0.73/0.94      (![X0 : $i, X1 : $i]:
% 0.73/0.94         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.73/0.94      inference('simplify', [status(thm)], ['12'])).
% 0.73/0.94  thf(t63_zfmisc_1, conjecture,
% 0.73/0.94    (![A:$i,B:$i,C:$i]:
% 0.73/0.94     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.73/0.94       ( r2_hidden @ A @ C ) ))).
% 0.73/0.94  thf(zf_stmt_3, negated_conjecture,
% 0.73/0.94    (~( ![A:$i,B:$i,C:$i]:
% 0.73/0.94        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.73/0.94          ( r2_hidden @ A @ C ) ) )),
% 0.73/0.94    inference('cnf.neg', [status(esa)], [t63_zfmisc_1])).
% 0.73/0.94  thf('14', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 0.73/0.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.73/0.94  thf('15', plain, ((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1)),
% 0.73/0.94      inference('sup-', [status(thm)], ['13', '14'])).
% 0.73/0.94  thf('16', plain,
% 0.73/0.94      (![X8 : $i, X9 : $i]:
% 0.73/0.94         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.73/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.73/0.94  thf(t1_xboole_0, axiom,
% 0.73/0.94    (![A:$i,B:$i,C:$i]:
% 0.73/0.94     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.73/0.94       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.73/0.94  thf('17', plain,
% 0.73/0.94      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.73/0.94         ((r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X7))
% 0.73/0.94          | (r2_hidden @ X4 @ X5)
% 0.73/0.94          | ~ (r2_hidden @ X4 @ X7))),
% 0.73/0.94      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.73/0.94  thf('18', plain,
% 0.73/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.94         ((r1_xboole_0 @ X0 @ X1)
% 0.73/0.94          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.73/0.94          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k5_xboole_0 @ X2 @ X0)))),
% 0.73/0.94      inference('sup-', [status(thm)], ['16', '17'])).
% 0.73/0.94  thf('19', plain,
% 0.73/0.94      (![X8 : $i, X9 : $i]:
% 0.73/0.94         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.73/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.73/0.94  thf('20', plain,
% 0.73/0.94      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.73/0.94         = (k2_tarski @ sk_A @ sk_B))),
% 0.73/0.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.73/0.94  thf(t95_xboole_1, axiom,
% 0.73/0.94    (![A:$i,B:$i]:
% 0.73/0.94     ( ( k3_xboole_0 @ A @ B ) =
% 0.73/0.94       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.73/0.94  thf('21', plain,
% 0.73/0.94      (![X18 : $i, X19 : $i]:
% 0.73/0.94         ((k3_xboole_0 @ X18 @ X19)
% 0.73/0.94           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 0.73/0.94              (k2_xboole_0 @ X18 @ X19)))),
% 0.73/0.94      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.73/0.94  thf(commutativity_k5_xboole_0, axiom,
% 0.73/0.94    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.73/0.94  thf('22', plain,
% 0.73/0.94      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.73/0.94      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.73/0.94  thf('23', plain,
% 0.73/0.94      (![X18 : $i, X19 : $i]:
% 0.73/0.94         ((k3_xboole_0 @ X18 @ X19)
% 0.73/0.94           = (k5_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ 
% 0.73/0.94              (k5_xboole_0 @ X18 @ X19)))),
% 0.73/0.94      inference('demod', [status(thm)], ['21', '22'])).
% 0.73/0.94  thf('24', plain,
% 0.73/0.94      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.73/0.94         ((r2_hidden @ X4 @ X5)
% 0.73/0.94          | (r2_hidden @ X4 @ X6)
% 0.73/0.94          | ~ (r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 0.73/0.94      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.73/0.94  thf('25', plain,
% 0.73/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.94         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.73/0.94          | (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ X0))
% 0.73/0.94          | (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.73/0.94      inference('sup-', [status(thm)], ['23', '24'])).
% 0.73/0.94  thf('26', plain,
% 0.73/0.94      (![X0 : $i]:
% 0.73/0.94         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.73/0.94          | (r2_hidden @ X0 @ 
% 0.73/0.94             (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.73/0.94          | (r2_hidden @ X0 @ 
% 0.73/0.94             (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.73/0.94      inference('sup-', [status(thm)], ['20', '25'])).
% 0.73/0.94  thf('27', plain,
% 0.73/0.94      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.73/0.94      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.73/0.94  thf('28', plain,
% 0.73/0.94      (![X0 : $i]:
% 0.73/0.94         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.73/0.94          | (r2_hidden @ X0 @ 
% 0.73/0.94             (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.73/0.94          | (r2_hidden @ X0 @ 
% 0.73/0.94             (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.73/0.94      inference('demod', [status(thm)], ['26', '27'])).
% 0.73/0.94  thf('29', plain,
% 0.73/0.94      (![X0 : $i]:
% 0.73/0.94         ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 0.73/0.94          | (r2_hidden @ (sk_C @ X0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.73/0.94             (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))
% 0.73/0.94          | (r2_hidden @ (sk_C @ X0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.73/0.94             (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.73/0.94      inference('sup-', [status(thm)], ['19', '28'])).
% 0.73/0.94  thf('30', plain,
% 0.73/0.94      (![X8 : $i, X9 : $i]:
% 0.73/0.94         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.73/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.73/0.94  thf('31', plain,
% 0.73/0.94      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.73/0.94         (~ (r2_hidden @ X10 @ X8)
% 0.73/0.94          | ~ (r2_hidden @ X10 @ X11)
% 0.73/0.94          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.73/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.73/0.94  thf('32', plain,
% 0.73/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.94         ((r1_xboole_0 @ X0 @ X1)
% 0.73/0.94          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.73/0.94          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.73/0.94      inference('sup-', [status(thm)], ['30', '31'])).
% 0.73/0.94  thf('33', plain,
% 0.73/0.94      (![X0 : $i]:
% 0.73/0.94         ((r2_hidden @ (sk_C @ X0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.73/0.94           (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.73/0.94          | (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 0.73/0.94          | ~ (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.73/0.94               (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))
% 0.73/0.94          | (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0))),
% 0.73/0.94      inference('sup-', [status(thm)], ['29', '32'])).
% 0.73/0.94  thf('34', plain,
% 0.73/0.94      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.73/0.94         = (k2_tarski @ sk_A @ sk_B))),
% 0.73/0.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.73/0.94  thf(l97_xboole_1, axiom,
% 0.73/0.94    (![A:$i,B:$i]:
% 0.73/0.94     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.73/0.94  thf('35', plain,
% 0.73/0.94      (![X12 : $i, X13 : $i]:
% 0.73/0.94         (r1_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k5_xboole_0 @ X12 @ X13))),
% 0.73/0.94      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.73/0.94  thf('36', plain,
% 0.73/0.94      ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.73/0.94        (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.73/0.94      inference('sup+', [status(thm)], ['34', '35'])).
% 0.73/0.94  thf('37', plain,
% 0.73/0.94      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.73/0.94      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.73/0.94  thf('38', plain,
% 0.73/0.94      ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.73/0.94        (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.73/0.94      inference('demod', [status(thm)], ['36', '37'])).
% 0.73/0.94  thf('39', plain,
% 0.73/0.94      (![X0 : $i]:
% 0.73/0.94         ((r2_hidden @ (sk_C @ X0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.73/0.94           (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.73/0.94          | (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 0.73/0.94          | (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0))),
% 0.73/0.94      inference('demod', [status(thm)], ['33', '38'])).
% 0.73/0.94  thf('40', plain,
% 0.73/0.94      (![X0 : $i]:
% 0.73/0.94         ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 0.73/0.94          | (r2_hidden @ (sk_C @ X0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.73/0.94             (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.73/0.94      inference('simplify', [status(thm)], ['39'])).
% 0.73/0.94  thf('41', plain,
% 0.73/0.94      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.73/0.94         = (k2_tarski @ sk_A @ sk_B))),
% 0.73/0.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.73/0.94  thf('42', plain,
% 0.73/0.94      (![X18 : $i, X19 : $i]:
% 0.73/0.94         ((k3_xboole_0 @ X18 @ X19)
% 0.73/0.94           = (k5_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ 
% 0.73/0.94              (k5_xboole_0 @ X18 @ X19)))),
% 0.73/0.94      inference('demod', [status(thm)], ['21', '22'])).
% 0.73/0.94  thf('43', plain,
% 0.73/0.94      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.73/0.94         (~ (r2_hidden @ X4 @ X5)
% 0.73/0.94          | ~ (r2_hidden @ X4 @ X6)
% 0.73/0.94          | ~ (r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 0.73/0.94      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.73/0.94  thf('44', plain,
% 0.73/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.94         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.73/0.94          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ X0))
% 0.73/0.94          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.73/0.94      inference('sup-', [status(thm)], ['42', '43'])).
% 0.73/0.94  thf('45', plain,
% 0.73/0.94      (![X0 : $i]:
% 0.73/0.94         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.73/0.94          | ~ (r2_hidden @ X0 @ 
% 0.73/0.94               (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.73/0.94          | ~ (r2_hidden @ X0 @ 
% 0.73/0.94               (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.73/0.94      inference('sup-', [status(thm)], ['41', '44'])).
% 0.73/0.94  thf('46', plain,
% 0.73/0.94      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.73/0.94      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.73/0.94  thf('47', plain,
% 0.73/0.94      (![X0 : $i]:
% 0.73/0.94         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.73/0.94          | ~ (r2_hidden @ X0 @ 
% 0.73/0.94               (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.73/0.94          | ~ (r2_hidden @ X0 @ 
% 0.73/0.94               (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.73/0.94      inference('demod', [status(thm)], ['45', '46'])).
% 0.73/0.94  thf('48', plain,
% 0.73/0.94      (![X0 : $i]:
% 0.73/0.94         ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 0.73/0.94          | ~ (r2_hidden @ (sk_C @ X0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.73/0.94               (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))
% 0.73/0.94          | ~ (r2_hidden @ (sk_C @ X0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.73/0.94               (k2_tarski @ sk_A @ sk_B)))),
% 0.73/0.94      inference('sup-', [status(thm)], ['40', '47'])).
% 0.73/0.94  thf('49', plain,
% 0.73/0.94      (![X8 : $i, X9 : $i]:
% 0.73/0.94         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.73/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.73/0.94  thf('50', plain,
% 0.73/0.94      (![X0 : $i]:
% 0.73/0.94         (~ (r2_hidden @ (sk_C @ X0 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.73/0.94             (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))
% 0.73/0.94          | (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0))),
% 0.73/0.94      inference('clc', [status(thm)], ['48', '49'])).
% 0.73/0.94  thf('51', plain,
% 0.73/0.94      (![X0 : $i]:
% 0.73/0.94         ((r2_hidden @ (sk_C @ X0 @ (k2_tarski @ sk_A @ sk_B)) @ sk_C_1)
% 0.73/0.94          | (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 0.73/0.94          | (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0))),
% 0.73/0.94      inference('sup-', [status(thm)], ['18', '50'])).
% 0.73/0.94  thf('52', plain,
% 0.73/0.94      (![X0 : $i]:
% 0.73/0.94         ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 0.73/0.94          | (r2_hidden @ (sk_C @ X0 @ (k2_tarski @ sk_A @ sk_B)) @ sk_C_1))),
% 0.73/0.94      inference('simplify', [status(thm)], ['51'])).
% 0.73/0.94  thf('53', plain,
% 0.73/0.94      (![X8 : $i, X9 : $i]:
% 0.73/0.94         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 0.73/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.73/0.94  thf('54', plain,
% 0.73/0.94      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.73/0.94         (~ (r2_hidden @ X10 @ X8)
% 0.73/0.94          | ~ (r2_hidden @ X10 @ X11)
% 0.73/0.94          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.73/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.73/0.94  thf('55', plain,
% 0.73/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.94         ((r1_xboole_0 @ X1 @ X0)
% 0.73/0.94          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.73/0.94          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.73/0.94      inference('sup-', [status(thm)], ['53', '54'])).
% 0.73/0.94  thf('56', plain,
% 0.73/0.94      (![X0 : $i]:
% 0.73/0.94         ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 0.73/0.94          | ~ (r1_xboole_0 @ X0 @ sk_C_1)
% 0.73/0.94          | (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0))),
% 0.73/0.94      inference('sup-', [status(thm)], ['52', '55'])).
% 0.73/0.94  thf('57', plain,
% 0.73/0.94      (![X0 : $i]:
% 0.73/0.94         (~ (r1_xboole_0 @ X0 @ sk_C_1)
% 0.73/0.94          | (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0))),
% 0.73/0.94      inference('simplify', [status(thm)], ['56'])).
% 0.73/0.94  thf('58', plain,
% 0.73/0.94      ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_A))),
% 0.73/0.94      inference('sup-', [status(thm)], ['15', '57'])).
% 0.73/0.94  thf('59', plain,
% 0.73/0.94      (![X52 : $i, X53 : $i]:
% 0.73/0.94         ((k1_enumset1 @ X52 @ X52 @ X53) = (k2_tarski @ X52 @ X53))),
% 0.73/0.94      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.73/0.94  thf('60', plain,
% 0.73/0.94      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.73/0.94         ((zip_tseitin_0 @ X25 @ X26 @ X27 @ X28)
% 0.73/0.94          | (r2_hidden @ X25 @ X29)
% 0.73/0.94          | ((X29) != (k1_enumset1 @ X28 @ X27 @ X26)))),
% 0.73/0.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.73/0.94  thf('61', plain,
% 0.73/0.94      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.73/0.94         ((r2_hidden @ X25 @ (k1_enumset1 @ X28 @ X27 @ X26))
% 0.73/0.94          | (zip_tseitin_0 @ X25 @ X26 @ X27 @ X28))),
% 0.73/0.94      inference('simplify', [status(thm)], ['60'])).
% 0.73/0.94  thf('62', plain,
% 0.73/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.94         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.73/0.94          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.73/0.94      inference('sup+', [status(thm)], ['59', '61'])).
% 0.73/0.94  thf('63', plain,
% 0.73/0.94      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.73/0.94         (((X21) != (X20)) | ~ (zip_tseitin_0 @ X21 @ X22 @ X23 @ X20))),
% 0.73/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.94  thf('64', plain,
% 0.73/0.94      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.73/0.94         ~ (zip_tseitin_0 @ X20 @ X22 @ X23 @ X20)),
% 0.73/0.94      inference('simplify', [status(thm)], ['63'])).
% 0.73/0.94  thf('65', plain,
% 0.73/0.94      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.73/0.94      inference('sup-', [status(thm)], ['62', '64'])).
% 0.73/0.94  thf('66', plain,
% 0.73/0.94      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.73/0.94         (~ (r2_hidden @ X10 @ X8)
% 0.73/0.94          | ~ (r2_hidden @ X10 @ X11)
% 0.73/0.94          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.73/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.73/0.94  thf('67', plain,
% 0.73/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.94         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.73/0.94          | ~ (r2_hidden @ X1 @ X2))),
% 0.73/0.94      inference('sup-', [status(thm)], ['65', '66'])).
% 0.73/0.94  thf('68', plain, (~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))),
% 0.73/0.94      inference('sup-', [status(thm)], ['58', '67'])).
% 0.73/0.94  thf('69', plain,
% 0.73/0.94      (![X51 : $i]: ((k2_tarski @ X51 @ X51) = (k1_tarski @ X51))),
% 0.73/0.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.73/0.94  thf('70', plain,
% 0.73/0.94      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.73/0.94      inference('sup-', [status(thm)], ['62', '64'])).
% 0.73/0.94  thf('71', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.73/0.94      inference('sup+', [status(thm)], ['69', '70'])).
% 0.73/0.94  thf('72', plain, ($false), inference('demod', [status(thm)], ['68', '71'])).
% 0.73/0.94  
% 0.73/0.94  % SZS output end Refutation
% 0.73/0.94  
% 0.73/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
