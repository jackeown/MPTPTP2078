%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dpqfYRexgV

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:47 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 454 expanded)
%              Number of leaves         :   30 ( 142 expanded)
%              Depth                    :   24
%              Number of atoms          :  875 (4563 expanded)
%              Number of equality atoms :  120 ( 602 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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

thf('1',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 )
      | ( X22 = X23 )
      | ( X22 = X24 )
      | ( X22 = X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X65: $i,X67: $i,X68: $i] :
      ( ( r1_tarski @ X67 @ ( k2_tarski @ X65 @ X68 ) )
      | ( X67
       != ( k1_tarski @ X65 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('3',plain,(
    ! [X65: $i,X68: $i] :
      ( r1_tarski @ ( k1_tarski @ X65 ) @ ( k2_tarski @ X65 @ X68 ) ) ),
    inference(simplify,[status(thm)],['2'])).

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

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D ) )
    = ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B_1 ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( X67
        = ( k2_tarski @ X65 @ X66 ) )
      | ( X67
        = ( k1_tarski @ X66 ) )
      | ( X67
        = ( k1_tarski @ X65 ) )
      | ( X67 = k1_xboole_0 )
      | ~ ( r1_tarski @ X67 @ ( k2_tarski @ X65 @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('13',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_D ) )
    | ( ( k1_tarski @ sk_A )
      = ( k2_tarski @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
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

thf('15',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ X26 @ X30 )
      | ( X30
       != ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X26 @ ( k1_enumset1 @ X29 @ X28 @ X27 ) )
      | ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X22 != X21 )
      | ~ ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ~ ( zip_tseitin_0 @ X21 @ X23 @ X24 @ X21 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_D ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('23',plain,(
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ~ ( zip_tseitin_0 @ X31 @ X27 @ X28 @ X29 )
      | ( X30
       != ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,(
    ! [X27: $i,X28: $i,X29: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X27 @ X28 @ X29 )
      | ~ ( r2_hidden @ X31 @ ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_D ) )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,
    ( ( sk_C_1 = sk_A )
    | ( sk_C_1 = sk_A )
    | ( sk_C_1 = sk_A )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_D ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','28'])).

thf('30',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_D ) )
    | ( sk_C_1 = sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('32',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_D @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('38',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C_1 ) )
    | ~ ( zip_tseitin_0 @ sk_D @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_D = sk_A )
    | ( sk_D = sk_A )
    | ( sk_D = sk_A )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C_1 ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','38'])).

thf('40',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C_1 ) )
    | ( sk_D = sk_A ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('42',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 )
      | ( X22 = X23 )
      | ( X22 = X24 )
      | ( X22 = X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('44',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('51',plain,
    ( ( ( sk_B @ ( k1_tarski @ sk_A ) )
      = sk_C_1 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_A = sk_C_1 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( ( k1_tarski @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = sk_C_1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('55',plain,
    ( ( ( k1_tarski @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','55'])).

thf('57',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('60',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('61',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('66',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('68',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('69',plain,(
    ! [X18: $i] :
      ( r1_xboole_0 @ X18 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('71',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['67','68','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dpqfYRexgV
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:57:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 750 iterations in 0.208s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.66  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.46/0.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.66  thf(d1_enumset1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.66       ( ![E:$i]:
% 0.46/0.66         ( ( r2_hidden @ E @ D ) <=>
% 0.46/0.66           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, axiom,
% 0.46/0.66    (![E:$i,C:$i,B:$i,A:$i]:
% 0.46/0.66     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.46/0.66       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.66         ((zip_tseitin_0 @ X22 @ X23 @ X24 @ X25)
% 0.46/0.66          | ((X22) = (X23))
% 0.46/0.66          | ((X22) = (X24))
% 0.46/0.66          | ((X22) = (X25)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.66         ((zip_tseitin_0 @ X22 @ X23 @ X24 @ X25)
% 0.46/0.66          | ((X22) = (X23))
% 0.46/0.66          | ((X22) = (X24))
% 0.46/0.66          | ((X22) = (X25)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(l45_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.46/0.66       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.46/0.66            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X65 : $i, X67 : $i, X68 : $i]:
% 0.46/0.66         ((r1_tarski @ X67 @ (k2_tarski @ X65 @ X68))
% 0.46/0.66          | ((X67) != (k1_tarski @ X65)))),
% 0.46/0.66      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X65 : $i, X68 : $i]:
% 0.46/0.66         (r1_tarski @ (k1_tarski @ X65) @ (k2_tarski @ X65 @ X68))),
% 0.46/0.66      inference('simplify', [status(thm)], ['2'])).
% 0.46/0.66  thf(t28_zfmisc_1, conjecture,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.46/0.66          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_1, negated_conjecture,
% 0.46/0.66    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.46/0.66             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ (k2_tarski @ sk_C_1 @ sk_D))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf(t28_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i]:
% 0.46/0.66         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.46/0.66      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ 
% 0.46/0.66         (k2_tarski @ sk_C_1 @ sk_D)) = (k2_tarski @ sk_A @ sk_B_1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.66  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.66  thf(t18_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.66         ((r1_tarski @ X10 @ X11)
% 0.46/0.66          | ~ (r1_tarski @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B_1))
% 0.46/0.66          | (r1_tarski @ X0 @ (k2_tarski @ sk_C_1 @ sk_D)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['6', '9'])).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D))),
% 0.46/0.66      inference('sup-', [status(thm)], ['3', '10'])).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.46/0.66         (((X67) = (k2_tarski @ X65 @ X66))
% 0.46/0.66          | ((X67) = (k1_tarski @ X66))
% 0.46/0.66          | ((X67) = (k1_tarski @ X65))
% 0.46/0.66          | ((X67) = (k1_xboole_0))
% 0.46/0.66          | ~ (r1_tarski @ X67 @ (k2_tarski @ X65 @ X66)))),
% 0.46/0.66      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C_1))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_D))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k2_tarski @ sk_C_1 @ sk_D)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.66  thf(t70_enumset1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X38 : $i, X39 : $i]:
% 0.46/0.66         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.46/0.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.66  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_3, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.66       ( ![E:$i]:
% 0.46/0.66         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.66         ((zip_tseitin_0 @ X26 @ X27 @ X28 @ X29)
% 0.46/0.66          | (r2_hidden @ X26 @ X30)
% 0.46/0.66          | ((X30) != (k1_enumset1 @ X29 @ X28 @ X27)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.66         ((r2_hidden @ X26 @ (k1_enumset1 @ X29 @ X28 @ X27))
% 0.46/0.66          | (zip_tseitin_0 @ X26 @ X27 @ X28 @ X29))),
% 0.46/0.66      inference('simplify', [status(thm)], ['15'])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.46/0.66          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['14', '16'])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.66         (((X22) != (X21)) | ~ (zip_tseitin_0 @ X22 @ X23 @ X24 @ X21))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.46/0.66         ~ (zip_tseitin_0 @ X21 @ X23 @ X24 @ X21)),
% 0.46/0.66      inference('simplify', [status(thm)], ['18'])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['17', '19'])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (((r2_hidden @ sk_C_1 @ (k1_tarski @ sk_A))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_D))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C_1))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['13', '20'])).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      (![X38 : $i, X39 : $i]:
% 0.46/0.66         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.46/0.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.66  thf(t69_enumset1, axiom,
% 0.46/0.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['22', '23'])).
% 0.46/0.66  thf('25', plain,
% 0.46/0.66      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X31 @ X30)
% 0.46/0.66          | ~ (zip_tseitin_0 @ X31 @ X27 @ X28 @ X29)
% 0.46/0.66          | ((X30) != (k1_enumset1 @ X29 @ X28 @ X27)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      (![X27 : $i, X28 : $i, X29 : $i, X31 : $i]:
% 0.46/0.66         (~ (zip_tseitin_0 @ X31 @ X27 @ X28 @ X29)
% 0.46/0.66          | ~ (r2_hidden @ X31 @ (k1_enumset1 @ X29 @ X28 @ X27)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['25'])).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.46/0.66          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['24', '26'])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C_1))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_D))
% 0.46/0.66        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_A @ sk_A @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['21', '27'])).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      ((((sk_C_1) = (sk_A))
% 0.46/0.66        | ((sk_C_1) = (sk_A))
% 0.46/0.66        | ((sk_C_1) = (sk_A))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_D))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C_1))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['1', '28'])).
% 0.46/0.66  thf('30', plain,
% 0.46/0.66      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C_1))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_D))
% 0.46/0.66        | ((sk_C_1) = (sk_A)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['29'])).
% 0.46/0.66  thf('31', plain, (((sk_A) != (sk_C_1))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C_1))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_D)))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['17', '19'])).
% 0.46/0.66  thf('35', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      (((r2_hidden @ sk_D @ (k1_tarski @ sk_A))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C_1))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['32', '35'])).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.46/0.66          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['24', '26'])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C_1))
% 0.46/0.66        | ~ (zip_tseitin_0 @ sk_D @ sk_A @ sk_A @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['36', '37'])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      ((((sk_D) = (sk_A))
% 0.46/0.66        | ((sk_D) = (sk_A))
% 0.46/0.66        | ((sk_D) = (sk_A))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C_1))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['0', '38'])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C_1))
% 0.46/0.66        | ((sk_D) = (sk_A)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['39'])).
% 0.46/0.66  thf('41', plain, (((sk_A) != (sk_D))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C_1)))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.66         ((zip_tseitin_0 @ X22 @ X23 @ X24 @ X25)
% 0.46/0.66          | ((X22) = (X23))
% 0.46/0.66          | ((X22) = (X24))
% 0.46/0.66          | ((X22) = (X25)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t7_xboole_0, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.66          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.46/0.66          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['24', '26'])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.66          | ~ (zip_tseitin_0 @ (sk_B @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.46/0.66          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.46/0.66          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.46/0.66          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['43', '46'])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.66          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['47'])).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C_1)))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.46/0.66  thf('50', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.46/0.66          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['47'])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      ((((sk_B @ (k1_tarski @ sk_A)) = (sk_C_1))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.46/0.66        | ((k1_tarski @ sk_C_1) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['49', '50'])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      ((((sk_A) = (sk_C_1))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.46/0.66        | ((k1_tarski @ sk_C_1) = (k1_xboole_0))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['48', '51'])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      ((((k1_tarski @ sk_C_1) = (k1_xboole_0))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.46/0.66        | ((sk_A) = (sk_C_1)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['52'])).
% 0.46/0.66  thf('54', plain, (((sk_A) != (sk_C_1))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      ((((k1_tarski @ sk_C_1) = (k1_xboole_0))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.46/0.66  thf('56', plain,
% 0.46/0.66      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.46/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['42', '55'])).
% 0.46/0.66  thf('57', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['56'])).
% 0.46/0.66  thf('58', plain,
% 0.46/0.66      (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['17', '19'])).
% 0.46/0.66  thf(idempotence_k3_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.66  thf('60', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.46/0.66      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.46/0.66  thf(t4_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.66            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.66       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.66            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.46/0.66  thf('61', plain,
% 0.46/0.66      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.46/0.66          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.46/0.66      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.66  thf('63', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['59', '62'])).
% 0.46/0.66  thf('64', plain,
% 0.46/0.66      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['58', '63'])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.66  thf('66', plain,
% 0.46/0.66      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['64', '65'])).
% 0.46/0.66  thf('67', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.46/0.66      inference('sup-', [status(thm)], ['57', '66'])).
% 0.46/0.66  thf('68', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['56'])).
% 0.46/0.66  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.46/0.66  thf('69', plain, (![X18 : $i]: (r1_xboole_0 @ X18 @ k1_xboole_0)),
% 0.46/0.66      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.46/0.66  thf('70', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.66  thf('71', plain,
% 0.46/0.66      (![X3 : $i, X4 : $i]:
% 0.46/0.66         ((r1_xboole_0 @ X3 @ X4)
% 0.46/0.66          | (r2_hidden @ (sk_C @ X4 @ X3) @ (k3_xboole_0 @ X3 @ X4)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.66  thf('72', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.46/0.66          | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['70', '71'])).
% 0.46/0.66  thf('73', plain,
% 0.46/0.66      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.46/0.66          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.46/0.66      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.66  thf('74', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['72', '73'])).
% 0.46/0.66  thf('75', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.46/0.66      inference('sup-', [status(thm)], ['69', '74'])).
% 0.46/0.66  thf('76', plain, ($false),
% 0.46/0.66      inference('demod', [status(thm)], ['67', '68', '75'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
