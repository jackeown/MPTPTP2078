%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E7AccbBR1L

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:48 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 113 expanded)
%              Number of leaves         :   38 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  662 ( 832 expanded)
%              Number of equality atoms :   70 (  90 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 )
      | ( X22 = X23 )
      | ( X22 = X24 )
      | ( X22 = X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X47: $i,X48: $i] :
      ( r1_tarski @ ( k1_tarski @ X47 ) @ ( k2_tarski @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D ) )
    = ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B_1 ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('16',plain,(
    ! [X18: $i] :
      ( r1_xboole_0 @ X18 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('27',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','29','30'])).

thf('32',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['15','31','32'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('35',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k2_enumset1 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X33 @ X34 @ X35 ) @ ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('37',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k2_enumset1 @ X40 @ X40 @ X41 @ X42 )
      = ( k1_enumset1 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_enumset1 @ sk_C_1 @ sk_D @ sk_A )
    = ( k2_tarski @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['33','38'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ X26 @ X30 )
      | ( X30
       != ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X26 @ ( k1_enumset1 @ X29 @ X28 @ X27 ) )
      | ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_C_1 @ sk_D ) )
      | ( zip_tseitin_0 @ X0 @ sk_A @ sk_D @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('44',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ~ ( zip_tseitin_0 @ X31 @ X27 @ X28 @ X29 )
      | ( X30
       != ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,(
    ! [X27: $i,X28: $i,X29: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X27 @ X28 @ X29 )
      | ~ ( r2_hidden @ X31 @ ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_A @ sk_D @ sk_C_1 )
      | ~ ( zip_tseitin_0 @ X0 @ sk_D @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_C_1 )
      | ( X0 = sk_C_1 )
      | ( X0 = sk_D )
      | ( zip_tseitin_0 @ X0 @ sk_A @ sk_D @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_A @ sk_D @ sk_C_1 )
      | ( X0 = sk_D )
      | ( X0 = sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X22 != X23 )
      | ~ ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ~ ( zip_tseitin_0 @ X23 @ X23 @ X24 @ X21 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('54',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E7AccbBR1L
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:24:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.58/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.75  % Solved by: fo/fo7.sh
% 0.58/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.75  % done 633 iterations in 0.289s
% 0.58/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.75  % SZS output start Refutation
% 0.58/0.75  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.58/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.75  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.58/0.75  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.58/0.75  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.75  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.58/0.75  thf(sk_B_type, type, sk_B: $i > $i).
% 0.58/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.75  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.58/0.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.75  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.58/0.75  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.58/0.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.75  thf(d1_enumset1, axiom,
% 0.58/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.75     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.58/0.75       ( ![E:$i]:
% 0.58/0.75         ( ( r2_hidden @ E @ D ) <=>
% 0.58/0.75           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.58/0.75  thf(zf_stmt_0, axiom,
% 0.58/0.75    (![E:$i,C:$i,B:$i,A:$i]:
% 0.58/0.75     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.58/0.75       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.58/0.75  thf('0', plain,
% 0.58/0.75      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.58/0.75         ((zip_tseitin_0 @ X22 @ X23 @ X24 @ X25)
% 0.58/0.75          | ((X22) = (X23))
% 0.58/0.75          | ((X22) = (X24))
% 0.58/0.75          | ((X22) = (X25)))),
% 0.58/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.75  thf(t12_zfmisc_1, axiom,
% 0.58/0.75    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.58/0.75  thf('1', plain,
% 0.58/0.75      (![X47 : $i, X48 : $i]:
% 0.58/0.75         (r1_tarski @ (k1_tarski @ X47) @ (k2_tarski @ X47 @ X48))),
% 0.58/0.75      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.58/0.75  thf(t28_zfmisc_1, conjecture,
% 0.58/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.75     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.58/0.75          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.58/0.75  thf(zf_stmt_1, negated_conjecture,
% 0.58/0.75    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.75        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.58/0.75             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.58/0.75    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.58/0.75  thf('2', plain,
% 0.58/0.75      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ (k2_tarski @ sk_C_1 @ sk_D))),
% 0.58/0.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.75  thf(t28_xboole_1, axiom,
% 0.58/0.75    (![A:$i,B:$i]:
% 0.58/0.75     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.58/0.75  thf('3', plain,
% 0.58/0.75      (![X13 : $i, X14 : $i]:
% 0.58/0.75         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.58/0.75      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.75  thf('4', plain,
% 0.58/0.75      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ 
% 0.58/0.75         (k2_tarski @ sk_C_1 @ sk_D)) = (k2_tarski @ sk_A @ sk_B_1))),
% 0.58/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.75  thf(commutativity_k3_xboole_0, axiom,
% 0.58/0.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.58/0.75  thf('5', plain,
% 0.58/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.75  thf(t18_xboole_1, axiom,
% 0.58/0.75    (![A:$i,B:$i,C:$i]:
% 0.58/0.75     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.58/0.75  thf('6', plain,
% 0.58/0.75      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.58/0.75         ((r1_tarski @ X10 @ X11)
% 0.58/0.75          | ~ (r1_tarski @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.58/0.75      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.58/0.75  thf('7', plain,
% 0.58/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.75         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.58/0.75      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.75  thf('8', plain,
% 0.58/0.75      (![X0 : $i]:
% 0.58/0.75         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B_1))
% 0.58/0.75          | (r1_tarski @ X0 @ (k2_tarski @ sk_C_1 @ sk_D)))),
% 0.58/0.75      inference('sup-', [status(thm)], ['4', '7'])).
% 0.58/0.75  thf('9', plain,
% 0.58/0.75      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D))),
% 0.58/0.75      inference('sup-', [status(thm)], ['1', '8'])).
% 0.58/0.75  thf('10', plain,
% 0.58/0.75      (![X13 : $i, X14 : $i]:
% 0.58/0.75         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.58/0.75      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.75  thf('11', plain,
% 0.58/0.75      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D))
% 0.58/0.75         = (k1_tarski @ sk_A))),
% 0.58/0.75      inference('sup-', [status(thm)], ['9', '10'])).
% 0.58/0.75  thf(t100_xboole_1, axiom,
% 0.58/0.75    (![A:$i,B:$i]:
% 0.58/0.75     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.58/0.75  thf('12', plain,
% 0.58/0.75      (![X8 : $i, X9 : $i]:
% 0.58/0.75         ((k4_xboole_0 @ X8 @ X9)
% 0.58/0.75           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.58/0.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.75  thf('13', plain,
% 0.58/0.75      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D))
% 0.58/0.75         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.58/0.75      inference('sup+', [status(thm)], ['11', '12'])).
% 0.58/0.75  thf(t98_xboole_1, axiom,
% 0.58/0.75    (![A:$i,B:$i]:
% 0.58/0.75     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.58/0.75  thf('14', plain,
% 0.58/0.75      (![X19 : $i, X20 : $i]:
% 0.58/0.75         ((k2_xboole_0 @ X19 @ X20)
% 0.58/0.75           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.58/0.75      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.58/0.75  thf('15', plain,
% 0.58/0.75      (((k2_xboole_0 @ (k2_tarski @ sk_C_1 @ sk_D) @ (k1_tarski @ sk_A))
% 0.58/0.75         = (k5_xboole_0 @ (k2_tarski @ sk_C_1 @ sk_D) @ 
% 0.58/0.75            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.58/0.75      inference('sup+', [status(thm)], ['13', '14'])).
% 0.58/0.75  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.58/0.75  thf('16', plain, (![X18 : $i]: (r1_xboole_0 @ X18 @ k1_xboole_0)),
% 0.58/0.75      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.58/0.75  thf(t7_xboole_0, axiom,
% 0.58/0.75    (![A:$i]:
% 0.58/0.75     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.58/0.75          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.58/0.75  thf('17', plain,
% 0.58/0.75      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.58/0.75      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.75  thf(t4_xboole_0, axiom,
% 0.58/0.75    (![A:$i,B:$i]:
% 0.58/0.75     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.58/0.75            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.58/0.75       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.58/0.75            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.58/0.75  thf('18', plain,
% 0.58/0.75      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.58/0.75         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.58/0.75          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.58/0.75      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.58/0.75  thf('19', plain,
% 0.58/0.75      (![X0 : $i, X1 : $i]:
% 0.58/0.75         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.58/0.75      inference('sup-', [status(thm)], ['17', '18'])).
% 0.58/0.75  thf('20', plain,
% 0.58/0.75      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.75      inference('sup-', [status(thm)], ['16', '19'])).
% 0.58/0.75  thf('21', plain,
% 0.58/0.75      (![X8 : $i, X9 : $i]:
% 0.58/0.75         ((k4_xboole_0 @ X8 @ X9)
% 0.58/0.75           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.58/0.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.75  thf('22', plain,
% 0.58/0.75      (![X0 : $i]:
% 0.58/0.75         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.75      inference('sup+', [status(thm)], ['20', '21'])).
% 0.58/0.75  thf(t5_boole, axiom,
% 0.58/0.75    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.58/0.75  thf('23', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.58/0.75      inference('cnf', [status(esa)], [t5_boole])).
% 0.58/0.75  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.58/0.75      inference('demod', [status(thm)], ['22', '23'])).
% 0.58/0.75  thf(t48_xboole_1, axiom,
% 0.58/0.75    (![A:$i,B:$i]:
% 0.58/0.75     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.58/0.75  thf('25', plain,
% 0.58/0.75      (![X15 : $i, X16 : $i]:
% 0.58/0.75         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.58/0.75           = (k3_xboole_0 @ X15 @ X16))),
% 0.58/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.75  thf('26', plain,
% 0.58/0.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.75      inference('sup+', [status(thm)], ['24', '25'])).
% 0.58/0.75  thf(idempotence_k3_xboole_0, axiom,
% 0.58/0.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.58/0.75  thf('27', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.58/0.75      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.58/0.75  thf('28', plain,
% 0.58/0.75      (![X8 : $i, X9 : $i]:
% 0.58/0.75         ((k4_xboole_0 @ X8 @ X9)
% 0.58/0.75           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.58/0.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.75  thf('29', plain,
% 0.58/0.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.58/0.75      inference('sup+', [status(thm)], ['27', '28'])).
% 0.58/0.75  thf('30', plain,
% 0.58/0.75      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.75      inference('sup-', [status(thm)], ['16', '19'])).
% 0.58/0.75  thf('31', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.75      inference('demod', [status(thm)], ['26', '29', '30'])).
% 0.58/0.75  thf('32', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.58/0.75      inference('cnf', [status(esa)], [t5_boole])).
% 0.58/0.75  thf('33', plain,
% 0.58/0.75      (((k2_xboole_0 @ (k2_tarski @ sk_C_1 @ sk_D) @ (k1_tarski @ sk_A))
% 0.58/0.75         = (k2_tarski @ sk_C_1 @ sk_D))),
% 0.58/0.75      inference('demod', [status(thm)], ['15', '31', '32'])).
% 0.58/0.75  thf(t70_enumset1, axiom,
% 0.58/0.75    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.58/0.75  thf('34', plain,
% 0.58/0.75      (![X38 : $i, X39 : $i]:
% 0.58/0.75         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.58/0.75      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.75  thf(t46_enumset1, axiom,
% 0.58/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.75     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.58/0.75       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.58/0.75  thf('35', plain,
% 0.58/0.75      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.58/0.75         ((k2_enumset1 @ X33 @ X34 @ X35 @ X36)
% 0.58/0.75           = (k2_xboole_0 @ (k1_enumset1 @ X33 @ X34 @ X35) @ (k1_tarski @ X36)))),
% 0.58/0.75      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.58/0.75  thf('36', plain,
% 0.58/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.75         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.58/0.75           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.58/0.75      inference('sup+', [status(thm)], ['34', '35'])).
% 0.58/0.75  thf(t71_enumset1, axiom,
% 0.58/0.75    (![A:$i,B:$i,C:$i]:
% 0.58/0.75     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.58/0.75  thf('37', plain,
% 0.58/0.75      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.58/0.75         ((k2_enumset1 @ X40 @ X40 @ X41 @ X42)
% 0.58/0.75           = (k1_enumset1 @ X40 @ X41 @ X42))),
% 0.58/0.75      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.58/0.75  thf('38', plain,
% 0.58/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.75         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.58/0.75           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.58/0.75      inference('sup+', [status(thm)], ['36', '37'])).
% 0.58/0.75  thf('39', plain,
% 0.58/0.75      (((k1_enumset1 @ sk_C_1 @ sk_D @ sk_A) = (k2_tarski @ sk_C_1 @ sk_D))),
% 0.58/0.75      inference('demod', [status(thm)], ['33', '38'])).
% 0.58/0.75  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.58/0.75  thf(zf_stmt_3, axiom,
% 0.58/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.75     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.58/0.75       ( ![E:$i]:
% 0.58/0.75         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.58/0.75  thf('40', plain,
% 0.58/0.75      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.58/0.75         ((zip_tseitin_0 @ X26 @ X27 @ X28 @ X29)
% 0.58/0.75          | (r2_hidden @ X26 @ X30)
% 0.58/0.75          | ((X30) != (k1_enumset1 @ X29 @ X28 @ X27)))),
% 0.58/0.75      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.75  thf('41', plain,
% 0.58/0.75      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.58/0.75         ((r2_hidden @ X26 @ (k1_enumset1 @ X29 @ X28 @ X27))
% 0.58/0.75          | (zip_tseitin_0 @ X26 @ X27 @ X28 @ X29))),
% 0.58/0.75      inference('simplify', [status(thm)], ['40'])).
% 0.58/0.75  thf('42', plain,
% 0.58/0.75      (![X0 : $i]:
% 0.58/0.75         ((r2_hidden @ X0 @ (k2_tarski @ sk_C_1 @ sk_D))
% 0.58/0.75          | (zip_tseitin_0 @ X0 @ sk_A @ sk_D @ sk_C_1))),
% 0.58/0.75      inference('sup+', [status(thm)], ['39', '41'])).
% 0.58/0.75  thf('43', plain,
% 0.58/0.75      (![X38 : $i, X39 : $i]:
% 0.58/0.75         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.58/0.75      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.75  thf('44', plain,
% 0.58/0.75      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.58/0.75         (~ (r2_hidden @ X31 @ X30)
% 0.58/0.75          | ~ (zip_tseitin_0 @ X31 @ X27 @ X28 @ X29)
% 0.58/0.75          | ((X30) != (k1_enumset1 @ X29 @ X28 @ X27)))),
% 0.58/0.75      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.75  thf('45', plain,
% 0.58/0.75      (![X27 : $i, X28 : $i, X29 : $i, X31 : $i]:
% 0.58/0.75         (~ (zip_tseitin_0 @ X31 @ X27 @ X28 @ X29)
% 0.58/0.75          | ~ (r2_hidden @ X31 @ (k1_enumset1 @ X29 @ X28 @ X27)))),
% 0.58/0.75      inference('simplify', [status(thm)], ['44'])).
% 0.58/0.75  thf('46', plain,
% 0.58/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.75         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.58/0.75          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.58/0.75      inference('sup-', [status(thm)], ['43', '45'])).
% 0.58/0.75  thf('47', plain,
% 0.58/0.75      (![X0 : $i]:
% 0.58/0.75         ((zip_tseitin_0 @ X0 @ sk_A @ sk_D @ sk_C_1)
% 0.58/0.75          | ~ (zip_tseitin_0 @ X0 @ sk_D @ sk_C_1 @ sk_C_1))),
% 0.58/0.75      inference('sup-', [status(thm)], ['42', '46'])).
% 0.58/0.75  thf('48', plain,
% 0.58/0.75      (![X0 : $i]:
% 0.58/0.75         (((X0) = (sk_C_1))
% 0.58/0.75          | ((X0) = (sk_C_1))
% 0.58/0.75          | ((X0) = (sk_D))
% 0.58/0.75          | (zip_tseitin_0 @ X0 @ sk_A @ sk_D @ sk_C_1))),
% 0.58/0.75      inference('sup-', [status(thm)], ['0', '47'])).
% 0.58/0.75  thf('49', plain,
% 0.58/0.75      (![X0 : $i]:
% 0.58/0.75         ((zip_tseitin_0 @ X0 @ sk_A @ sk_D @ sk_C_1)
% 0.58/0.75          | ((X0) = (sk_D))
% 0.58/0.75          | ((X0) = (sk_C_1)))),
% 0.58/0.75      inference('simplify', [status(thm)], ['48'])).
% 0.58/0.75  thf('50', plain,
% 0.58/0.75      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.58/0.75         (((X22) != (X23)) | ~ (zip_tseitin_0 @ X22 @ X23 @ X24 @ X21))),
% 0.58/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.75  thf('51', plain,
% 0.58/0.75      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.58/0.75         ~ (zip_tseitin_0 @ X23 @ X23 @ X24 @ X21)),
% 0.58/0.75      inference('simplify', [status(thm)], ['50'])).
% 0.58/0.75  thf('52', plain, ((((sk_A) = (sk_C_1)) | ((sk_A) = (sk_D)))),
% 0.58/0.75      inference('sup-', [status(thm)], ['49', '51'])).
% 0.58/0.75  thf('53', plain, (((sk_A) != (sk_D))),
% 0.58/0.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.75  thf('54', plain, (((sk_A) != (sk_C_1))),
% 0.58/0.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.75  thf('55', plain, ($false),
% 0.58/0.75      inference('simplify_reflect-', [status(thm)], ['52', '53', '54'])).
% 0.58/0.75  
% 0.58/0.75  % SZS output end Refutation
% 0.58/0.75  
% 0.58/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
