%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gW8U28Y8fi

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:58 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 139 expanded)
%              Number of leaves         :   21 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  863 (1414 expanded)
%              Number of equality atoms :   75 ( 122 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X18 @ X22 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X13 @ X15 @ X16 @ X13 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(l2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r2_hidden @ C @ A )
        | ( r1_tarski @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) ) ) )).

thf('17',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ( r2_hidden @ X33 @ X31 )
      | ( r1_tarski @ X31 @ ( k4_xboole_0 @ X32 @ ( k1_tarski @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[l2_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('20',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( X14 = X15 )
      | ( X14 = X16 )
      | ( X14 = X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('37',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('38',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('39',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( zip_tseitin_0 @ X23 @ X19 @ X20 @ X21 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X19 @ X20 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ sk_B )
          = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) )
        | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_B ) @ X0 @ ( k1_tarski @ sk_B ) ) @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,
    ( ( ~ ( r2_hidden @ sk_B @ sk_A )
      | ( ( k1_tarski @ sk_B )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
      | ( ( k1_tarski @ sk_B )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,
    ( ( ( ( k1_tarski @ sk_B )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','54'])).

thf('56',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['33','58'])).

thf('60',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['48'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('62',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['48'])).

thf('66',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','59','60','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gW8U28Y8fi
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:25:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.13/1.35  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.13/1.35  % Solved by: fo/fo7.sh
% 1.13/1.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.13/1.35  % done 969 iterations in 0.879s
% 1.13/1.35  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.13/1.35  % SZS output start Refutation
% 1.13/1.35  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.13/1.35  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.13/1.35  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.13/1.35  thf(sk_B_type, type, sk_B: $i).
% 1.13/1.35  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.13/1.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.13/1.35  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.13/1.35  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.13/1.35  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.13/1.35  thf(sk_A_type, type, sk_A: $i).
% 1.13/1.35  thf(t65_zfmisc_1, conjecture,
% 1.13/1.35    (![A:$i,B:$i]:
% 1.13/1.35     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.13/1.35       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.13/1.35  thf(zf_stmt_0, negated_conjecture,
% 1.13/1.35    (~( ![A:$i,B:$i]:
% 1.13/1.35        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.13/1.35          ( ~( r2_hidden @ B @ A ) ) ) )),
% 1.13/1.35    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 1.13/1.35  thf('0', plain,
% 1.13/1.35      (((r2_hidden @ sk_B @ sk_A)
% 1.13/1.35        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('1', plain,
% 1.13/1.35      (((r2_hidden @ sk_B @ sk_A)) | 
% 1.13/1.35       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.13/1.35      inference('split', [status(esa)], ['0'])).
% 1.13/1.35  thf(t70_enumset1, axiom,
% 1.13/1.35    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.13/1.35  thf('2', plain,
% 1.13/1.35      (![X26 : $i, X27 : $i]:
% 1.13/1.35         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 1.13/1.35      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.13/1.35  thf(d1_enumset1, axiom,
% 1.13/1.35    (![A:$i,B:$i,C:$i,D:$i]:
% 1.13/1.35     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.13/1.35       ( ![E:$i]:
% 1.13/1.35         ( ( r2_hidden @ E @ D ) <=>
% 1.13/1.35           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.13/1.35  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.13/1.35  thf(zf_stmt_2, axiom,
% 1.13/1.35    (![E:$i,C:$i,B:$i,A:$i]:
% 1.13/1.35     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.13/1.35       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.13/1.35  thf(zf_stmt_3, axiom,
% 1.13/1.35    (![A:$i,B:$i,C:$i,D:$i]:
% 1.13/1.35     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.13/1.35       ( ![E:$i]:
% 1.13/1.35         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.13/1.35  thf('3', plain,
% 1.13/1.35      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.13/1.35         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 1.13/1.35          | (r2_hidden @ X18 @ X22)
% 1.13/1.35          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.13/1.35  thf('4', plain,
% 1.13/1.35      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.13/1.35         ((r2_hidden @ X18 @ (k1_enumset1 @ X21 @ X20 @ X19))
% 1.13/1.35          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21))),
% 1.13/1.35      inference('simplify', [status(thm)], ['3'])).
% 1.13/1.35  thf('5', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.35         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.13/1.35          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.13/1.35      inference('sup+', [status(thm)], ['2', '4'])).
% 1.13/1.35  thf('6', plain,
% 1.13/1.35      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.13/1.35         (((X14) != (X13)) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.13/1.35  thf('7', plain,
% 1.13/1.35      (![X13 : $i, X15 : $i, X16 : $i]:
% 1.13/1.35         ~ (zip_tseitin_0 @ X13 @ X15 @ X16 @ X13)),
% 1.13/1.35      inference('simplify', [status(thm)], ['6'])).
% 1.13/1.35  thf('8', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.13/1.35      inference('sup-', [status(thm)], ['5', '7'])).
% 1.13/1.35  thf(t69_enumset1, axiom,
% 1.13/1.35    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.13/1.35  thf('9', plain, (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 1.13/1.35      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.13/1.35  thf(d5_xboole_0, axiom,
% 1.13/1.35    (![A:$i,B:$i,C:$i]:
% 1.13/1.35     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.13/1.35       ( ![D:$i]:
% 1.13/1.35         ( ( r2_hidden @ D @ C ) <=>
% 1.13/1.35           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.13/1.35  thf('10', plain,
% 1.13/1.35      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.13/1.35         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.13/1.35          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.13/1.35          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.13/1.35      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.13/1.35  thf('11', plain,
% 1.13/1.35      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.13/1.35         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.13/1.35          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.13/1.35          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.13/1.35      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.13/1.35  thf('12', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.13/1.35          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.13/1.35          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.13/1.35          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['10', '11'])).
% 1.13/1.35  thf('13', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.13/1.35          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.13/1.35      inference('simplify', [status(thm)], ['12'])).
% 1.13/1.35  thf('14', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.13/1.35          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.13/1.35      inference('simplify', [status(thm)], ['12'])).
% 1.13/1.35  thf(d10_xboole_0, axiom,
% 1.13/1.35    (![A:$i,B:$i]:
% 1.13/1.35     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.13/1.35  thf('15', plain,
% 1.13/1.35      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 1.13/1.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.13/1.35  thf('16', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 1.13/1.35      inference('simplify', [status(thm)], ['15'])).
% 1.13/1.35  thf(l2_zfmisc_1, axiom,
% 1.13/1.35    (![A:$i,B:$i,C:$i]:
% 1.13/1.35     ( ( r1_tarski @ A @ B ) =>
% 1.13/1.35       ( ( r2_hidden @ C @ A ) | 
% 1.13/1.35         ( r1_tarski @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) ) ))).
% 1.13/1.35  thf('17', plain,
% 1.13/1.35      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.13/1.35         (~ (r1_tarski @ X31 @ X32)
% 1.13/1.35          | (r2_hidden @ X33 @ X31)
% 1.13/1.35          | (r1_tarski @ X31 @ (k4_xboole_0 @ X32 @ (k1_tarski @ X33))))),
% 1.13/1.35      inference('cnf', [status(esa)], [l2_zfmisc_1])).
% 1.13/1.35  thf('18', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         ((r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 1.13/1.35          | (r2_hidden @ X1 @ X0))),
% 1.13/1.35      inference('sup-', [status(thm)], ['16', '17'])).
% 1.13/1.35  thf(t36_xboole_1, axiom,
% 1.13/1.35    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.13/1.35  thf('19', plain,
% 1.13/1.35      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 1.13/1.35      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.13/1.35  thf('20', plain,
% 1.13/1.35      (![X6 : $i, X8 : $i]:
% 1.13/1.35         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.13/1.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.13/1.35  thf('21', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.13/1.35          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['19', '20'])).
% 1.13/1.35  thf('22', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         ((r2_hidden @ X0 @ X1)
% 1.13/1.35          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.13/1.35      inference('sup-', [status(thm)], ['18', '21'])).
% 1.13/1.35  thf('23', plain,
% 1.13/1.35      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.13/1.35         (~ (r2_hidden @ X4 @ X3)
% 1.13/1.35          | ~ (r2_hidden @ X4 @ X2)
% 1.13/1.35          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.13/1.35      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.13/1.35  thf('24', plain,
% 1.13/1.35      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.13/1.35         (~ (r2_hidden @ X4 @ X2)
% 1.13/1.35          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.13/1.35      inference('simplify', [status(thm)], ['23'])).
% 1.13/1.35  thf('25', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.35         (~ (r2_hidden @ X2 @ X0)
% 1.13/1.35          | (r2_hidden @ X1 @ X0)
% 1.13/1.35          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['22', '24'])).
% 1.13/1.35  thf('26', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.35         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 1.13/1.35          | (r2_hidden @ X0 @ X2)
% 1.13/1.35          | ~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ X1) @ X2))),
% 1.13/1.35      inference('sup-', [status(thm)], ['14', '25'])).
% 1.13/1.35  thf('27', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 1.13/1.35          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.13/1.35          | ((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['13', '26'])).
% 1.13/1.35  thf('28', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.13/1.35          | ((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 1.13/1.35      inference('simplify', [status(thm)], ['27'])).
% 1.13/1.35  thf('29', plain,
% 1.13/1.35      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.13/1.35         (~ (r2_hidden @ X4 @ X2)
% 1.13/1.35          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.13/1.35      inference('simplify', [status(thm)], ['23'])).
% 1.13/1.35  thf('30', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.35         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 1.13/1.35          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.13/1.35          | ~ (r2_hidden @ X2 @ X1))),
% 1.13/1.35      inference('sup-', [status(thm)], ['28', '29'])).
% 1.13/1.35  thf('31', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.13/1.35          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.13/1.35      inference('condensation', [status(thm)], ['30'])).
% 1.13/1.35  thf('32', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 1.13/1.35          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['9', '31'])).
% 1.13/1.35  thf('33', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.13/1.35      inference('sup-', [status(thm)], ['8', '32'])).
% 1.13/1.35  thf('34', plain,
% 1.13/1.35      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 1.13/1.35      inference('split', [status(esa)], ['0'])).
% 1.13/1.35  thf('35', plain,
% 1.13/1.35      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.13/1.35         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 1.13/1.35          | ((X14) = (X15))
% 1.13/1.35          | ((X14) = (X16))
% 1.13/1.35          | ((X14) = (X17)))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.13/1.35  thf('36', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.13/1.35          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.13/1.35      inference('simplify', [status(thm)], ['12'])).
% 1.13/1.35  thf('37', plain,
% 1.13/1.35      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 1.13/1.35      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.13/1.35  thf('38', plain,
% 1.13/1.35      (![X26 : $i, X27 : $i]:
% 1.13/1.35         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 1.13/1.35      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.13/1.35  thf('39', plain,
% 1.13/1.35      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.13/1.35         (~ (r2_hidden @ X23 @ X22)
% 1.13/1.35          | ~ (zip_tseitin_0 @ X23 @ X19 @ X20 @ X21)
% 1.13/1.35          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.13/1.35  thf('40', plain,
% 1.13/1.35      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 1.13/1.35         (~ (zip_tseitin_0 @ X23 @ X19 @ X20 @ X21)
% 1.13/1.35          | ~ (r2_hidden @ X23 @ (k1_enumset1 @ X21 @ X20 @ X19)))),
% 1.13/1.35      inference('simplify', [status(thm)], ['39'])).
% 1.13/1.35  thf('41', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.35         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.13/1.35          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.13/1.35      inference('sup-', [status(thm)], ['38', '40'])).
% 1.13/1.35  thf('42', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.13/1.35          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.13/1.35      inference('sup-', [status(thm)], ['37', '41'])).
% 1.13/1.35  thf('43', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 1.13/1.35          | ~ (zip_tseitin_0 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X1) @ X0 @ X0 @ 
% 1.13/1.35               X0))),
% 1.13/1.35      inference('sup-', [status(thm)], ['36', '42'])).
% 1.13/1.35  thf('44', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))
% 1.13/1.35          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))
% 1.13/1.35          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))
% 1.13/1.35          | ((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['35', '43'])).
% 1.13/1.35  thf('45', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 1.13/1.35          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0)))),
% 1.13/1.35      inference('simplify', [status(thm)], ['44'])).
% 1.13/1.35  thf('46', plain,
% 1.13/1.35      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.13/1.35         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.13/1.35          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.13/1.35          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.13/1.35      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.13/1.35  thf('47', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.13/1.35          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.13/1.35      inference('eq_fact', [status(thm)], ['46'])).
% 1.13/1.35  thf('48', plain,
% 1.13/1.35      ((~ (r2_hidden @ sk_B @ sk_A)
% 1.13/1.35        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('49', plain,
% 1.13/1.35      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 1.13/1.35         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.13/1.35      inference('split', [status(esa)], ['48'])).
% 1.13/1.35  thf('50', plain,
% 1.13/1.35      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.13/1.35         (~ (r2_hidden @ X4 @ X2)
% 1.13/1.35          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.13/1.35      inference('simplify', [status(thm)], ['23'])).
% 1.13/1.35  thf('51', plain,
% 1.13/1.35      ((![X0 : $i]:
% 1.13/1.35          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 1.13/1.35         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.13/1.35      inference('sup-', [status(thm)], ['49', '50'])).
% 1.13/1.35  thf('52', plain,
% 1.13/1.35      ((![X0 : $i]:
% 1.13/1.35          (((k1_tarski @ sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_B) @ X0))
% 1.13/1.35           | ~ (r2_hidden @ 
% 1.13/1.35                (sk_D @ (k1_tarski @ sk_B) @ X0 @ (k1_tarski @ sk_B)) @ sk_A)))
% 1.13/1.35         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.13/1.35      inference('sup-', [status(thm)], ['47', '51'])).
% 1.13/1.35  thf('53', plain,
% 1.13/1.35      (((~ (r2_hidden @ sk_B @ sk_A)
% 1.13/1.35         | ((k1_tarski @ sk_B)
% 1.13/1.35             = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 1.13/1.35         | ((k1_tarski @ sk_B)
% 1.13/1.35             = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))))
% 1.13/1.35         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.13/1.35      inference('sup-', [status(thm)], ['45', '52'])).
% 1.13/1.35  thf('54', plain,
% 1.13/1.35      (((((k1_tarski @ sk_B)
% 1.13/1.35           = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 1.13/1.35         | ~ (r2_hidden @ sk_B @ sk_A)))
% 1.13/1.35         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.13/1.35      inference('simplify', [status(thm)], ['53'])).
% 1.13/1.35  thf('55', plain,
% 1.13/1.35      ((((k1_tarski @ sk_B)
% 1.13/1.35          = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))))
% 1.13/1.35         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 1.13/1.35             ((r2_hidden @ sk_B @ sk_A)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['34', '54'])).
% 1.13/1.35  thf('56', plain,
% 1.13/1.35      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.13/1.35         (~ (r2_hidden @ X4 @ X2)
% 1.13/1.35          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.13/1.35      inference('simplify', [status(thm)], ['23'])).
% 1.13/1.35  thf('57', plain,
% 1.13/1.35      ((![X0 : $i]:
% 1.13/1.35          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 1.13/1.35           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 1.13/1.35         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 1.13/1.35             ((r2_hidden @ sk_B @ sk_A)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['55', '56'])).
% 1.13/1.35  thf('58', plain,
% 1.13/1.35      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B)))
% 1.13/1.35         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 1.13/1.35             ((r2_hidden @ sk_B @ sk_A)))),
% 1.13/1.35      inference('simplify', [status(thm)], ['57'])).
% 1.13/1.35  thf('59', plain,
% 1.13/1.35      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 1.13/1.35       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['33', '58'])).
% 1.13/1.35  thf('60', plain,
% 1.13/1.35      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 1.13/1.35       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.13/1.35      inference('split', [status(esa)], ['48'])).
% 1.13/1.35  thf('61', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         ((r2_hidden @ X0 @ X1)
% 1.13/1.35          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.13/1.35      inference('sup-', [status(thm)], ['18', '21'])).
% 1.13/1.35  thf('62', plain,
% 1.13/1.35      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 1.13/1.35         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.13/1.35      inference('split', [status(esa)], ['0'])).
% 1.13/1.35  thf('63', plain,
% 1.13/1.35      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 1.13/1.35         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.13/1.35      inference('sup-', [status(thm)], ['61', '62'])).
% 1.13/1.35  thf('64', plain,
% 1.13/1.35      (((r2_hidden @ sk_B @ sk_A))
% 1.13/1.35         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.13/1.35      inference('simplify', [status(thm)], ['63'])).
% 1.13/1.35  thf('65', plain,
% 1.13/1.35      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 1.13/1.35      inference('split', [status(esa)], ['48'])).
% 1.13/1.35  thf('66', plain,
% 1.13/1.35      (((r2_hidden @ sk_B @ sk_A)) | 
% 1.13/1.35       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['64', '65'])).
% 1.13/1.35  thf('67', plain, ($false),
% 1.13/1.35      inference('sat_resolution*', [status(thm)], ['1', '59', '60', '66'])).
% 1.13/1.35  
% 1.13/1.35  % SZS output end Refutation
% 1.13/1.35  
% 1.13/1.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
