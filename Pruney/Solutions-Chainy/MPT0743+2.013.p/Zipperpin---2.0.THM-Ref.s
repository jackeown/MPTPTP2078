%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i4H9HHpzzr

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:54 EST 2020

% Result     : Theorem 2.83s
% Output     : Refutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  172 (2221 expanded)
%              Number of leaves         :   28 ( 644 expanded)
%              Depth                    :   40
%              Number of atoms          : 1216 (19266 expanded)
%              Number of equality atoms :   55 ( 661 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v3_ordinal1 @ X58 )
      | ( r1_ordinal1 @ X59 @ X58 )
      | ( r2_hidden @ X58 @ X59 )
      | ~ ( v3_ordinal1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X48: $i,X50: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X48 ) @ X50 )
      | ~ ( r2_hidden @ X48 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
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

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X8 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X8 @ X10 @ X11 @ X8 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('12',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( r2_hidden @ X61 @ X62 )
      | ~ ( r1_tarski @ X62 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t33_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ B )
            <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_ordinal1])).

thf('16',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('19',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('20',plain,(
    ! [X53: $i] :
      ( ( k1_ordinal1 @ X53 )
      = ( k2_xboole_0 @ X53 @ ( k1_tarski @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v3_ordinal1 @ X58 )
      | ( r1_ordinal1 @ X59 @ X58 )
      | ( r2_hidden @ X58 @ X59 )
      | ~ ( v3_ordinal1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('23',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('24',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( v3_ordinal1 @ X54 )
      | ~ ( v3_ordinal1 @ X55 )
      | ( r1_tarski @ X54 @ X55 )
      | ~ ( r1_ordinal1 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('29',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('33',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( v3_ordinal1 @ X56 )
      | ( r2_hidden @ X57 @ X56 )
      | ( X57 = X56 )
      | ( r2_hidden @ X56 @ X57 )
      | ~ ( v3_ordinal1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('34',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( r2_hidden @ X61 @ X62 )
      | ~ ( r1_tarski @ X62 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( sk_A = sk_B )
      | ( r2_hidden @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

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

thf('42',plain,
    ( ! [X0: $i] :
        ( ( sk_A = sk_B )
        | ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_A = sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['21','42'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('44',plain,(
    ! [X60: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X60 ) )
      | ~ ( v3_ordinal1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('45',plain,(
    ! [X60: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X60 ) )
      | ~ ( v3_ordinal1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('46',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('47',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( v3_ordinal1 @ X54 )
      | ~ ( v3_ordinal1 @ X55 )
      | ( r1_tarski @ X54 @ X55 )
      | ~ ( r1_ordinal1 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('49',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('56',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('58',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['44','58'])).

thf('60',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('61',plain,
    ( ( ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('63',plain,
    ( ( ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( sk_A = sk_B )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','63'])).

thf('65',plain,(
    ! [X53: $i] :
      ( ( k1_ordinal1 @ X53 )
      = ( k2_xboole_0 @ X53 @ ( k1_tarski @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('66',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('67',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('68',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','69'])).

thf('71',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( r2_hidden @ X61 @ X62 )
      | ~ ( r1_tarski @ X62 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('72',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_A = sk_B ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','72'])).

thf('74',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('75',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('77',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','69'])).

thf('79',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('80',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('82',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('84',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('85',plain,
    ( ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['82','85'])).

thf('87',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['18','86'])).

thf('88',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['17','87'])).

thf('89',plain,(
    ! [X60: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X60 ) )
      | ~ ( v3_ordinal1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('90',plain,(
    ! [X60: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X60 ) )
      | ~ ( v3_ordinal1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('91',plain,(
    ! [X60: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X60 ) )
      | ~ ( v3_ordinal1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('92',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v3_ordinal1 @ X58 )
      | ( r1_ordinal1 @ X59 @ X58 )
      | ( r2_hidden @ X58 @ X59 )
      | ~ ( v3_ordinal1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('93',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v3_ordinal1 @ X58 )
      | ( r1_ordinal1 @ X59 @ X58 )
      | ( r2_hidden @ X58 @ X59 )
      | ~ ( v3_ordinal1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['17','87'])).

thf('99',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('101',plain,
    ( ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','101'])).

thf('103',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('104',plain,(
    r1_ordinal1 @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( v3_ordinal1 @ X54 )
      | ~ ( v3_ordinal1 @ X55 )
      | ( r1_tarski @ X54 @ X55 )
      | ~ ( r1_ordinal1 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('106',plain,
    ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('108',plain,
    ( ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','108'])).

thf('110',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('111',plain,(
    r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('113',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('115',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['89','115'])).

thf('117',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('118',plain,
    ( ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X53: $i] :
      ( ( k1_ordinal1 @ X53 )
      = ( k2_xboole_0 @ X53 @ ( k1_tarski @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('120',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('121',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['119','121'])).

thf('123',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['118','122'])).

thf('124',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['46'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('126',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['46'])).

thf('128',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['18','86','127'])).

thf('129',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['126','128'])).

thf('130',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference(clc,[status(thm)],['123','129'])).

thf('131',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( r2_hidden @ X61 @ X62 )
      | ~ ( r1_tarski @ X62 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('132',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['46'])).

thf('134',plain,(
    ! [X48: $i,X50: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X48 ) @ X50 )
      | ~ ( r2_hidden @ X48 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('135',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['18','86','127'])).

thf('137',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k1_ordinal1 @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['132','137'])).

thf('139',plain,(
    ~ ( r1_ordinal1 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['88','138'])).

thf('140',plain,(
    ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','139'])).

thf('141',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['140','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i4H9HHpzzr
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:00:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 2.83/3.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.83/3.09  % Solved by: fo/fo7.sh
% 2.83/3.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.83/3.09  % done 5343 iterations in 2.628s
% 2.83/3.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.83/3.09  % SZS output start Refutation
% 2.83/3.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.83/3.09  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 2.83/3.09  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 2.83/3.09  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 2.83/3.09  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 2.83/3.09  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.83/3.09  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.83/3.09  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.83/3.09  thf(sk_A_type, type, sk_A: $i).
% 2.83/3.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.83/3.09  thf(sk_B_type, type, sk_B: $i).
% 2.83/3.09  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.83/3.09  thf(t26_ordinal1, axiom,
% 2.83/3.09    (![A:$i]:
% 2.83/3.09     ( ( v3_ordinal1 @ A ) =>
% 2.83/3.09       ( ![B:$i]:
% 2.83/3.09         ( ( v3_ordinal1 @ B ) =>
% 2.83/3.09           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 2.83/3.09  thf('0', plain,
% 2.83/3.09      (![X58 : $i, X59 : $i]:
% 2.83/3.09         (~ (v3_ordinal1 @ X58)
% 2.83/3.09          | (r1_ordinal1 @ X59 @ X58)
% 2.83/3.09          | (r2_hidden @ X58 @ X59)
% 2.83/3.09          | ~ (v3_ordinal1 @ X59))),
% 2.83/3.09      inference('cnf', [status(esa)], [t26_ordinal1])).
% 2.83/3.09  thf(l1_zfmisc_1, axiom,
% 2.83/3.09    (![A:$i,B:$i]:
% 2.83/3.09     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 2.83/3.09  thf('1', plain,
% 2.83/3.09      (![X48 : $i, X50 : $i]:
% 2.83/3.09         ((r1_tarski @ (k1_tarski @ X48) @ X50) | ~ (r2_hidden @ X48 @ X50))),
% 2.83/3.09      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 2.83/3.09  thf('2', plain,
% 2.83/3.09      (![X0 : $i, X1 : $i]:
% 2.83/3.09         (~ (v3_ordinal1 @ X0)
% 2.83/3.09          | (r1_ordinal1 @ X0 @ X1)
% 2.83/3.09          | ~ (v3_ordinal1 @ X1)
% 2.83/3.09          | (r1_tarski @ (k1_tarski @ X1) @ X0))),
% 2.83/3.09      inference('sup-', [status(thm)], ['0', '1'])).
% 2.83/3.09  thf(t69_enumset1, axiom,
% 2.83/3.09    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.83/3.09  thf('3', plain, (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 2.83/3.09      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.83/3.09  thf(t70_enumset1, axiom,
% 2.83/3.09    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.83/3.09  thf('4', plain,
% 2.83/3.09      (![X21 : $i, X22 : $i]:
% 2.83/3.09         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 2.83/3.09      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.83/3.09  thf(d1_enumset1, axiom,
% 2.83/3.09    (![A:$i,B:$i,C:$i,D:$i]:
% 2.83/3.09     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.83/3.09       ( ![E:$i]:
% 2.83/3.09         ( ( r2_hidden @ E @ D ) <=>
% 2.83/3.09           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 2.83/3.09  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 2.83/3.09  thf(zf_stmt_1, axiom,
% 2.83/3.09    (![E:$i,C:$i,B:$i,A:$i]:
% 2.83/3.09     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 2.83/3.09       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 2.83/3.09  thf(zf_stmt_2, axiom,
% 2.83/3.09    (![A:$i,B:$i,C:$i,D:$i]:
% 2.83/3.09     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.83/3.09       ( ![E:$i]:
% 2.83/3.09         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 2.83/3.09  thf('5', plain,
% 2.83/3.09      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 2.83/3.09         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 2.83/3.09          | (r2_hidden @ X13 @ X17)
% 2.83/3.09          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.83/3.09  thf('6', plain,
% 2.83/3.09      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 2.83/3.09         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 2.83/3.09          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 2.83/3.09      inference('simplify', [status(thm)], ['5'])).
% 2.83/3.09  thf('7', plain,
% 2.83/3.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.83/3.09         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.83/3.09          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 2.83/3.09      inference('sup+', [status(thm)], ['4', '6'])).
% 2.83/3.09  thf('8', plain,
% 2.83/3.09      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 2.83/3.09         (((X9) != (X8)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.83/3.09  thf('9', plain,
% 2.83/3.09      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X8 @ X10 @ X11 @ X8)),
% 2.83/3.09      inference('simplify', [status(thm)], ['8'])).
% 2.83/3.09  thf('10', plain,
% 2.83/3.09      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 2.83/3.09      inference('sup-', [status(thm)], ['7', '9'])).
% 2.83/3.09  thf('11', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.83/3.09      inference('sup+', [status(thm)], ['3', '10'])).
% 2.83/3.09  thf(t7_ordinal1, axiom,
% 2.83/3.09    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.83/3.09  thf('12', plain,
% 2.83/3.09      (![X61 : $i, X62 : $i]:
% 2.83/3.09         (~ (r2_hidden @ X61 @ X62) | ~ (r1_tarski @ X62 @ X61))),
% 2.83/3.09      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.83/3.09  thf('13', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 2.83/3.09      inference('sup-', [status(thm)], ['11', '12'])).
% 2.83/3.09  thf('14', plain,
% 2.83/3.09      (![X0 : $i]:
% 2.83/3.09         (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 2.83/3.09      inference('sup-', [status(thm)], ['2', '13'])).
% 2.83/3.09  thf('15', plain,
% 2.83/3.09      (![X0 : $i]: ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 2.83/3.09      inference('simplify', [status(thm)], ['14'])).
% 2.83/3.09  thf(t33_ordinal1, conjecture,
% 2.83/3.09    (![A:$i]:
% 2.83/3.09     ( ( v3_ordinal1 @ A ) =>
% 2.83/3.09       ( ![B:$i]:
% 2.83/3.09         ( ( v3_ordinal1 @ B ) =>
% 2.83/3.09           ( ( r2_hidden @ A @ B ) <=>
% 2.83/3.09             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 2.83/3.09  thf(zf_stmt_3, negated_conjecture,
% 2.83/3.09    (~( ![A:$i]:
% 2.83/3.09        ( ( v3_ordinal1 @ A ) =>
% 2.83/3.09          ( ![B:$i]:
% 2.83/3.09            ( ( v3_ordinal1 @ B ) =>
% 2.83/3.09              ( ( r2_hidden @ A @ B ) <=>
% 2.83/3.09                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 2.83/3.09    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 2.83/3.09  thf('16', plain,
% 2.83/3.09      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 2.83/3.09        | ~ (r2_hidden @ sk_A @ sk_B))),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.83/3.09  thf('17', plain,
% 2.83/3.09      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 2.83/3.09         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('split', [status(esa)], ['16'])).
% 2.83/3.09  thf('18', plain,
% 2.83/3.09      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 2.83/3.09       ~ ((r2_hidden @ sk_A @ sk_B))),
% 2.83/3.09      inference('split', [status(esa)], ['16'])).
% 2.83/3.09  thf('19', plain,
% 2.83/3.09      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 2.83/3.09      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.83/3.09  thf(d1_ordinal1, axiom,
% 2.83/3.09    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 2.83/3.09  thf('20', plain,
% 2.83/3.09      (![X53 : $i]:
% 2.83/3.09         ((k1_ordinal1 @ X53) = (k2_xboole_0 @ X53 @ (k1_tarski @ X53)))),
% 2.83/3.09      inference('cnf', [status(esa)], [d1_ordinal1])).
% 2.83/3.09  thf('21', plain,
% 2.83/3.09      (![X0 : $i]:
% 2.83/3.09         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 2.83/3.09      inference('sup+', [status(thm)], ['19', '20'])).
% 2.83/3.09  thf('22', plain,
% 2.83/3.09      (![X58 : $i, X59 : $i]:
% 2.83/3.09         (~ (v3_ordinal1 @ X58)
% 2.83/3.09          | (r1_ordinal1 @ X59 @ X58)
% 2.83/3.09          | (r2_hidden @ X58 @ X59)
% 2.83/3.09          | ~ (v3_ordinal1 @ X59))),
% 2.83/3.09      inference('cnf', [status(esa)], [t26_ordinal1])).
% 2.83/3.09  thf('23', plain,
% 2.83/3.09      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 2.83/3.09      inference('split', [status(esa)], ['16'])).
% 2.83/3.09  thf('24', plain,
% 2.83/3.09      (((~ (v3_ordinal1 @ sk_B)
% 2.83/3.09         | (r1_ordinal1 @ sk_B @ sk_A)
% 2.83/3.09         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['22', '23'])).
% 2.83/3.09  thf('25', plain, ((v3_ordinal1 @ sk_B)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.83/3.09  thf('26', plain, ((v3_ordinal1 @ sk_A)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.83/3.09  thf('27', plain,
% 2.83/3.09      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 2.83/3.09      inference('demod', [status(thm)], ['24', '25', '26'])).
% 2.83/3.09  thf(redefinition_r1_ordinal1, axiom,
% 2.83/3.09    (![A:$i,B:$i]:
% 2.83/3.09     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 2.83/3.09       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 2.83/3.09  thf('28', plain,
% 2.83/3.09      (![X54 : $i, X55 : $i]:
% 2.83/3.09         (~ (v3_ordinal1 @ X54)
% 2.83/3.09          | ~ (v3_ordinal1 @ X55)
% 2.83/3.09          | (r1_tarski @ X54 @ X55)
% 2.83/3.09          | ~ (r1_ordinal1 @ X54 @ X55))),
% 2.83/3.09      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 2.83/3.09  thf('29', plain,
% 2.83/3.09      ((((r1_tarski @ sk_B @ sk_A)
% 2.83/3.09         | ~ (v3_ordinal1 @ sk_A)
% 2.83/3.09         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['27', '28'])).
% 2.83/3.09  thf('30', plain, ((v3_ordinal1 @ sk_A)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.83/3.09  thf('31', plain, ((v3_ordinal1 @ sk_B)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.83/3.09  thf('32', plain,
% 2.83/3.09      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 2.83/3.09      inference('demod', [status(thm)], ['29', '30', '31'])).
% 2.83/3.09  thf(t24_ordinal1, axiom,
% 2.83/3.09    (![A:$i]:
% 2.83/3.09     ( ( v3_ordinal1 @ A ) =>
% 2.83/3.09       ( ![B:$i]:
% 2.83/3.09         ( ( v3_ordinal1 @ B ) =>
% 2.83/3.09           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 2.83/3.09                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 2.83/3.09  thf('33', plain,
% 2.83/3.09      (![X56 : $i, X57 : $i]:
% 2.83/3.09         (~ (v3_ordinal1 @ X56)
% 2.83/3.09          | (r2_hidden @ X57 @ X56)
% 2.83/3.09          | ((X57) = (X56))
% 2.83/3.09          | (r2_hidden @ X56 @ X57)
% 2.83/3.09          | ~ (v3_ordinal1 @ X57))),
% 2.83/3.09      inference('cnf', [status(esa)], [t24_ordinal1])).
% 2.83/3.09  thf('34', plain,
% 2.83/3.09      (![X61 : $i, X62 : $i]:
% 2.83/3.09         (~ (r2_hidden @ X61 @ X62) | ~ (r1_tarski @ X62 @ X61))),
% 2.83/3.09      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.83/3.09  thf('35', plain,
% 2.83/3.09      (![X0 : $i, X1 : $i]:
% 2.83/3.09         (~ (v3_ordinal1 @ X1)
% 2.83/3.09          | (r2_hidden @ X0 @ X1)
% 2.83/3.09          | ((X1) = (X0))
% 2.83/3.09          | ~ (v3_ordinal1 @ X0)
% 2.83/3.09          | ~ (r1_tarski @ X0 @ X1))),
% 2.83/3.09      inference('sup-', [status(thm)], ['33', '34'])).
% 2.83/3.09  thf('36', plain,
% 2.83/3.09      (((~ (v3_ordinal1 @ sk_B)
% 2.83/3.09         | ((sk_A) = (sk_B))
% 2.83/3.09         | (r2_hidden @ sk_B @ sk_A)
% 2.83/3.09         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['32', '35'])).
% 2.83/3.09  thf('37', plain, ((v3_ordinal1 @ sk_B)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.83/3.09  thf('38', plain, ((v3_ordinal1 @ sk_A)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.83/3.09  thf('39', plain,
% 2.83/3.09      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_B @ sk_A)))
% 2.83/3.09         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 2.83/3.09      inference('demod', [status(thm)], ['36', '37', '38'])).
% 2.83/3.09  thf(d3_xboole_0, axiom,
% 2.83/3.09    (![A:$i,B:$i,C:$i]:
% 2.83/3.09     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 2.83/3.09       ( ![D:$i]:
% 2.83/3.09         ( ( r2_hidden @ D @ C ) <=>
% 2.83/3.09           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.83/3.09  thf('40', plain,
% 2.83/3.09      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.83/3.09         (~ (r2_hidden @ X2 @ X5)
% 2.83/3.09          | (r2_hidden @ X2 @ X4)
% 2.83/3.09          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 2.83/3.09      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.83/3.09  thf('41', plain,
% 2.83/3.09      (![X2 : $i, X3 : $i, X5 : $i]:
% 2.83/3.09         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 2.83/3.09      inference('simplify', [status(thm)], ['40'])).
% 2.83/3.09  thf('42', plain,
% 2.83/3.09      ((![X0 : $i]:
% 2.83/3.09          (((sk_A) = (sk_B)) | (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_A @ X0))))
% 2.83/3.09         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['39', '41'])).
% 2.83/3.09  thf('43', plain,
% 2.83/3.09      ((((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A)) | ((sk_A) = (sk_B))))
% 2.83/3.09         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 2.83/3.09      inference('sup+', [status(thm)], ['21', '42'])).
% 2.83/3.09  thf(t29_ordinal1, axiom,
% 2.83/3.09    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 2.83/3.09  thf('44', plain,
% 2.83/3.09      (![X60 : $i]:
% 2.83/3.09         ((v3_ordinal1 @ (k1_ordinal1 @ X60)) | ~ (v3_ordinal1 @ X60))),
% 2.83/3.09      inference('cnf', [status(esa)], [t29_ordinal1])).
% 2.83/3.09  thf('45', plain,
% 2.83/3.09      (![X60 : $i]:
% 2.83/3.09         ((v3_ordinal1 @ (k1_ordinal1 @ X60)) | ~ (v3_ordinal1 @ X60))),
% 2.83/3.09      inference('cnf', [status(esa)], [t29_ordinal1])).
% 2.83/3.09  thf('46', plain,
% 2.83/3.09      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.83/3.09  thf('47', plain,
% 2.83/3.09      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 2.83/3.09         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('split', [status(esa)], ['46'])).
% 2.83/3.09  thf('48', plain,
% 2.83/3.09      (![X54 : $i, X55 : $i]:
% 2.83/3.09         (~ (v3_ordinal1 @ X54)
% 2.83/3.09          | ~ (v3_ordinal1 @ X55)
% 2.83/3.09          | (r1_tarski @ X54 @ X55)
% 2.83/3.09          | ~ (r1_ordinal1 @ X54 @ X55))),
% 2.83/3.09      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 2.83/3.09  thf('49', plain,
% 2.83/3.09      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 2.83/3.09         | ~ (v3_ordinal1 @ sk_B)
% 2.83/3.09         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 2.83/3.09         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['47', '48'])).
% 2.83/3.09  thf('50', plain, ((v3_ordinal1 @ sk_B)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.83/3.09  thf('51', plain,
% 2.83/3.09      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 2.83/3.09         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 2.83/3.09         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('demod', [status(thm)], ['49', '50'])).
% 2.83/3.09  thf('52', plain,
% 2.83/3.09      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 2.83/3.09         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['45', '51'])).
% 2.83/3.09  thf('53', plain, ((v3_ordinal1 @ sk_A)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.83/3.09  thf('54', plain,
% 2.83/3.09      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 2.83/3.09         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('demod', [status(thm)], ['52', '53'])).
% 2.83/3.09  thf('55', plain,
% 2.83/3.09      (![X0 : $i, X1 : $i]:
% 2.83/3.09         (~ (v3_ordinal1 @ X1)
% 2.83/3.09          | (r2_hidden @ X0 @ X1)
% 2.83/3.09          | ((X1) = (X0))
% 2.83/3.09          | ~ (v3_ordinal1 @ X0)
% 2.83/3.09          | ~ (r1_tarski @ X0 @ X1))),
% 2.83/3.09      inference('sup-', [status(thm)], ['33', '34'])).
% 2.83/3.09  thf('56', plain,
% 2.83/3.09      (((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 2.83/3.09         | ((sk_B) = (k1_ordinal1 @ sk_A))
% 2.83/3.09         | (r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)
% 2.83/3.09         | ~ (v3_ordinal1 @ sk_B)))
% 2.83/3.09         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['54', '55'])).
% 2.83/3.09  thf('57', plain, ((v3_ordinal1 @ sk_B)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.83/3.09  thf('58', plain,
% 2.83/3.09      (((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 2.83/3.09         | ((sk_B) = (k1_ordinal1 @ sk_A))
% 2.83/3.09         | (r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 2.83/3.09         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('demod', [status(thm)], ['56', '57'])).
% 2.83/3.09  thf('59', plain,
% 2.83/3.09      (((~ (v3_ordinal1 @ sk_A)
% 2.83/3.09         | (r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)
% 2.83/3.09         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 2.83/3.09         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['44', '58'])).
% 2.83/3.09  thf('60', plain, ((v3_ordinal1 @ sk_A)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.83/3.09  thf('61', plain,
% 2.83/3.09      ((((r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)
% 2.83/3.09         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 2.83/3.09         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('demod', [status(thm)], ['59', '60'])).
% 2.83/3.09  thf(antisymmetry_r2_hidden, axiom,
% 2.83/3.09    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 2.83/3.09  thf('62', plain,
% 2.83/3.09      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 2.83/3.09      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 2.83/3.09  thf('63', plain,
% 2.83/3.09      (((((sk_B) = (k1_ordinal1 @ sk_A))
% 2.83/3.09         | ~ (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))))
% 2.83/3.09         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['61', '62'])).
% 2.83/3.09  thf('64', plain,
% 2.83/3.09      (((((sk_A) = (sk_B)) | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 2.83/3.09         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 2.83/3.09             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['43', '63'])).
% 2.83/3.09  thf('65', plain,
% 2.83/3.09      (![X53 : $i]:
% 2.83/3.09         ((k1_ordinal1 @ X53) = (k2_xboole_0 @ X53 @ (k1_tarski @ X53)))),
% 2.83/3.09      inference('cnf', [status(esa)], [d1_ordinal1])).
% 2.83/3.09  thf('66', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.83/3.09      inference('sup+', [status(thm)], ['3', '10'])).
% 2.83/3.09  thf('67', plain,
% 2.83/3.09      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.83/3.09         (~ (r2_hidden @ X2 @ X3)
% 2.83/3.09          | (r2_hidden @ X2 @ X4)
% 2.83/3.09          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 2.83/3.09      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.83/3.09  thf('68', plain,
% 2.83/3.09      (![X2 : $i, X3 : $i, X5 : $i]:
% 2.83/3.09         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 2.83/3.09      inference('simplify', [status(thm)], ['67'])).
% 2.83/3.09  thf('69', plain,
% 2.83/3.09      (![X0 : $i, X1 : $i]:
% 2.83/3.09         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['66', '68'])).
% 2.83/3.09  thf('70', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 2.83/3.09      inference('sup+', [status(thm)], ['65', '69'])).
% 2.83/3.09  thf('71', plain,
% 2.83/3.09      (![X61 : $i, X62 : $i]:
% 2.83/3.09         (~ (r2_hidden @ X61 @ X62) | ~ (r1_tarski @ X62 @ X61))),
% 2.83/3.09      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.83/3.09  thf('72', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 2.83/3.09      inference('sup-', [status(thm)], ['70', '71'])).
% 2.83/3.09  thf('73', plain,
% 2.83/3.09      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_A) = (sk_B))))
% 2.83/3.09         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 2.83/3.09             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['64', '72'])).
% 2.83/3.09  thf('74', plain,
% 2.83/3.09      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 2.83/3.09      inference('demod', [status(thm)], ['29', '30', '31'])).
% 2.83/3.09  thf('75', plain,
% 2.83/3.09      ((((sk_A) = (sk_B)))
% 2.83/3.09         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 2.83/3.09             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('demod', [status(thm)], ['73', '74'])).
% 2.83/3.09  thf('76', plain,
% 2.83/3.09      (((((sk_B) = (k1_ordinal1 @ sk_A))
% 2.83/3.09         | ~ (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))))
% 2.83/3.09         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['61', '62'])).
% 2.83/3.09  thf('77', plain,
% 2.83/3.09      (((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A))
% 2.83/3.09         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 2.83/3.09         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 2.83/3.09             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['75', '76'])).
% 2.83/3.09  thf('78', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 2.83/3.09      inference('sup+', [status(thm)], ['65', '69'])).
% 2.83/3.09  thf('79', plain,
% 2.83/3.09      ((((sk_A) = (sk_B)))
% 2.83/3.09         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 2.83/3.09             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('demod', [status(thm)], ['73', '74'])).
% 2.83/3.09  thf('80', plain,
% 2.83/3.09      ((((sk_A) = (k1_ordinal1 @ sk_A)))
% 2.83/3.09         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 2.83/3.09             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('demod', [status(thm)], ['77', '78', '79'])).
% 2.83/3.09  thf('81', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 2.83/3.09      inference('sup-', [status(thm)], ['70', '71'])).
% 2.83/3.09  thf('82', plain,
% 2.83/3.09      ((~ (r1_tarski @ sk_A @ sk_A))
% 2.83/3.09         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 2.83/3.09             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['80', '81'])).
% 2.83/3.09  thf('83', plain,
% 2.83/3.09      ((((sk_A) = (sk_B)))
% 2.83/3.09         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 2.83/3.09             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('demod', [status(thm)], ['73', '74'])).
% 2.83/3.09  thf('84', plain,
% 2.83/3.09      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 2.83/3.09      inference('demod', [status(thm)], ['29', '30', '31'])).
% 2.83/3.09  thf('85', plain,
% 2.83/3.09      (((r1_tarski @ sk_A @ sk_A))
% 2.83/3.09         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 2.83/3.09             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 2.83/3.09      inference('sup+', [status(thm)], ['83', '84'])).
% 2.83/3.09  thf('86', plain,
% 2.83/3.09      (((r2_hidden @ sk_A @ sk_B)) | 
% 2.83/3.09       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 2.83/3.09      inference('demod', [status(thm)], ['82', '85'])).
% 2.83/3.09  thf('87', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 2.83/3.09      inference('sat_resolution*', [status(thm)], ['18', '86'])).
% 2.83/3.09  thf('88', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 2.83/3.09      inference('simpl_trail', [status(thm)], ['17', '87'])).
% 2.83/3.09  thf('89', plain,
% 2.83/3.09      (![X60 : $i]:
% 2.83/3.09         ((v3_ordinal1 @ (k1_ordinal1 @ X60)) | ~ (v3_ordinal1 @ X60))),
% 2.83/3.09      inference('cnf', [status(esa)], [t29_ordinal1])).
% 2.83/3.09  thf('90', plain,
% 2.83/3.09      (![X60 : $i]:
% 2.83/3.09         ((v3_ordinal1 @ (k1_ordinal1 @ X60)) | ~ (v3_ordinal1 @ X60))),
% 2.83/3.09      inference('cnf', [status(esa)], [t29_ordinal1])).
% 2.83/3.09  thf('91', plain,
% 2.83/3.09      (![X60 : $i]:
% 2.83/3.09         ((v3_ordinal1 @ (k1_ordinal1 @ X60)) | ~ (v3_ordinal1 @ X60))),
% 2.83/3.09      inference('cnf', [status(esa)], [t29_ordinal1])).
% 2.83/3.09  thf('92', plain,
% 2.83/3.09      (![X58 : $i, X59 : $i]:
% 2.83/3.09         (~ (v3_ordinal1 @ X58)
% 2.83/3.09          | (r1_ordinal1 @ X59 @ X58)
% 2.83/3.09          | (r2_hidden @ X58 @ X59)
% 2.83/3.09          | ~ (v3_ordinal1 @ X59))),
% 2.83/3.09      inference('cnf', [status(esa)], [t26_ordinal1])).
% 2.83/3.09  thf('93', plain,
% 2.83/3.09      (![X58 : $i, X59 : $i]:
% 2.83/3.09         (~ (v3_ordinal1 @ X58)
% 2.83/3.09          | (r1_ordinal1 @ X59 @ X58)
% 2.83/3.09          | (r2_hidden @ X58 @ X59)
% 2.83/3.09          | ~ (v3_ordinal1 @ X59))),
% 2.83/3.09      inference('cnf', [status(esa)], [t26_ordinal1])).
% 2.83/3.09  thf('94', plain,
% 2.83/3.09      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 2.83/3.09      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 2.83/3.09  thf('95', plain,
% 2.83/3.09      (![X0 : $i, X1 : $i]:
% 2.83/3.09         (~ (v3_ordinal1 @ X0)
% 2.83/3.09          | (r1_ordinal1 @ X0 @ X1)
% 2.83/3.09          | ~ (v3_ordinal1 @ X1)
% 2.83/3.09          | ~ (r2_hidden @ X0 @ X1))),
% 2.83/3.09      inference('sup-', [status(thm)], ['93', '94'])).
% 2.83/3.09  thf('96', plain,
% 2.83/3.09      (![X0 : $i, X1 : $i]:
% 2.83/3.09         (~ (v3_ordinal1 @ X0)
% 2.83/3.09          | (r1_ordinal1 @ X0 @ X1)
% 2.83/3.09          | ~ (v3_ordinal1 @ X1)
% 2.83/3.09          | ~ (v3_ordinal1 @ X0)
% 2.83/3.09          | (r1_ordinal1 @ X1 @ X0)
% 2.83/3.09          | ~ (v3_ordinal1 @ X1))),
% 2.83/3.09      inference('sup-', [status(thm)], ['92', '95'])).
% 2.83/3.09  thf('97', plain,
% 2.83/3.09      (![X0 : $i, X1 : $i]:
% 2.83/3.09         ((r1_ordinal1 @ X1 @ X0)
% 2.83/3.09          | ~ (v3_ordinal1 @ X1)
% 2.83/3.09          | (r1_ordinal1 @ X0 @ X1)
% 2.83/3.09          | ~ (v3_ordinal1 @ X0))),
% 2.83/3.09      inference('simplify', [status(thm)], ['96'])).
% 2.83/3.09  thf('98', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 2.83/3.09      inference('simpl_trail', [status(thm)], ['17', '87'])).
% 2.83/3.09  thf('99', plain,
% 2.83/3.09      ((~ (v3_ordinal1 @ sk_B)
% 2.83/3.09        | (r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))
% 2.83/3.09        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['97', '98'])).
% 2.83/3.09  thf('100', plain, ((v3_ordinal1 @ sk_B)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.83/3.09  thf('101', plain,
% 2.83/3.09      (((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))
% 2.83/3.09        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 2.83/3.09      inference('demod', [status(thm)], ['99', '100'])).
% 2.83/3.09  thf('102', plain,
% 2.83/3.09      ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['91', '101'])).
% 2.83/3.09  thf('103', plain, ((v3_ordinal1 @ sk_A)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.83/3.09  thf('104', plain, ((r1_ordinal1 @ sk_B @ (k1_ordinal1 @ sk_A))),
% 2.83/3.09      inference('demod', [status(thm)], ['102', '103'])).
% 2.83/3.09  thf('105', plain,
% 2.83/3.09      (![X54 : $i, X55 : $i]:
% 2.83/3.09         (~ (v3_ordinal1 @ X54)
% 2.83/3.09          | ~ (v3_ordinal1 @ X55)
% 2.83/3.09          | (r1_tarski @ X54 @ X55)
% 2.83/3.09          | ~ (r1_ordinal1 @ X54 @ X55))),
% 2.83/3.09      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 2.83/3.09  thf('106', plain,
% 2.83/3.09      (((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 2.83/3.09        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 2.83/3.09        | ~ (v3_ordinal1 @ sk_B))),
% 2.83/3.09      inference('sup-', [status(thm)], ['104', '105'])).
% 2.83/3.09  thf('107', plain, ((v3_ordinal1 @ sk_B)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.83/3.09  thf('108', plain,
% 2.83/3.09      (((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 2.83/3.09        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 2.83/3.09      inference('demod', [status(thm)], ['106', '107'])).
% 2.83/3.09  thf('109', plain,
% 2.83/3.09      ((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['90', '108'])).
% 2.83/3.09  thf('110', plain, ((v3_ordinal1 @ sk_A)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.83/3.09  thf('111', plain, ((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))),
% 2.83/3.09      inference('demod', [status(thm)], ['109', '110'])).
% 2.83/3.09  thf('112', plain,
% 2.83/3.09      (![X0 : $i, X1 : $i]:
% 2.83/3.09         (~ (v3_ordinal1 @ X1)
% 2.83/3.09          | (r2_hidden @ X0 @ X1)
% 2.83/3.09          | ((X1) = (X0))
% 2.83/3.09          | ~ (v3_ordinal1 @ X0)
% 2.83/3.09          | ~ (r1_tarski @ X0 @ X1))),
% 2.83/3.09      inference('sup-', [status(thm)], ['33', '34'])).
% 2.83/3.09  thf('113', plain,
% 2.83/3.09      ((~ (v3_ordinal1 @ sk_B)
% 2.83/3.09        | ((k1_ordinal1 @ sk_A) = (sk_B))
% 2.83/3.09        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 2.83/3.09        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['111', '112'])).
% 2.83/3.09  thf('114', plain, ((v3_ordinal1 @ sk_B)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.83/3.09  thf('115', plain,
% 2.83/3.09      ((((k1_ordinal1 @ sk_A) = (sk_B))
% 2.83/3.09        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 2.83/3.09        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 2.83/3.09      inference('demod', [status(thm)], ['113', '114'])).
% 2.83/3.09  thf('116', plain,
% 2.83/3.09      ((~ (v3_ordinal1 @ sk_A)
% 2.83/3.09        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 2.83/3.09        | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['89', '115'])).
% 2.83/3.09  thf('117', plain, ((v3_ordinal1 @ sk_A)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.83/3.09  thf('118', plain,
% 2.83/3.09      (((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 2.83/3.09        | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 2.83/3.09      inference('demod', [status(thm)], ['116', '117'])).
% 2.83/3.09  thf('119', plain,
% 2.83/3.09      (![X53 : $i]:
% 2.83/3.09         ((k1_ordinal1 @ X53) = (k2_xboole_0 @ X53 @ (k1_tarski @ X53)))),
% 2.83/3.09      inference('cnf', [status(esa)], [d1_ordinal1])).
% 2.83/3.09  thf('120', plain,
% 2.83/3.09      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.83/3.09         (~ (r2_hidden @ X6 @ X4)
% 2.83/3.09          | (r2_hidden @ X6 @ X5)
% 2.83/3.09          | (r2_hidden @ X6 @ X3)
% 2.83/3.09          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 2.83/3.09      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.83/3.09  thf('121', plain,
% 2.83/3.09      (![X3 : $i, X5 : $i, X6 : $i]:
% 2.83/3.09         ((r2_hidden @ X6 @ X3)
% 2.83/3.09          | (r2_hidden @ X6 @ X5)
% 2.83/3.09          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 2.83/3.09      inference('simplify', [status(thm)], ['120'])).
% 2.83/3.09  thf('122', plain,
% 2.83/3.09      (![X0 : $i, X1 : $i]:
% 2.83/3.09         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 2.83/3.09          | (r2_hidden @ X1 @ X0)
% 2.83/3.09          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['119', '121'])).
% 2.83/3.09  thf('123', plain,
% 2.83/3.09      ((((k1_ordinal1 @ sk_A) = (sk_B))
% 2.83/3.09        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 2.83/3.09        | (r2_hidden @ sk_B @ sk_A))),
% 2.83/3.09      inference('sup-', [status(thm)], ['118', '122'])).
% 2.83/3.09  thf('124', plain,
% 2.83/3.09      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 2.83/3.09      inference('split', [status(esa)], ['46'])).
% 2.83/3.09  thf('125', plain,
% 2.83/3.09      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 2.83/3.09      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 2.83/3.09  thf('126', plain,
% 2.83/3.09      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['124', '125'])).
% 2.83/3.09  thf('127', plain,
% 2.83/3.09      (((r2_hidden @ sk_A @ sk_B)) | 
% 2.83/3.09       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 2.83/3.09      inference('split', [status(esa)], ['46'])).
% 2.83/3.09  thf('128', plain, (((r2_hidden @ sk_A @ sk_B))),
% 2.83/3.09      inference('sat_resolution*', [status(thm)], ['18', '86', '127'])).
% 2.83/3.09  thf('129', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 2.83/3.09      inference('simpl_trail', [status(thm)], ['126', '128'])).
% 2.83/3.09  thf('130', plain,
% 2.83/3.09      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 2.83/3.09        | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 2.83/3.09      inference('clc', [status(thm)], ['123', '129'])).
% 2.83/3.09  thf('131', plain,
% 2.83/3.09      (![X61 : $i, X62 : $i]:
% 2.83/3.09         (~ (r2_hidden @ X61 @ X62) | ~ (r1_tarski @ X62 @ X61))),
% 2.83/3.09      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.83/3.09  thf('132', plain,
% 2.83/3.09      ((((k1_ordinal1 @ sk_A) = (sk_B))
% 2.83/3.09        | ~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 2.83/3.09      inference('sup-', [status(thm)], ['130', '131'])).
% 2.83/3.09  thf('133', plain,
% 2.83/3.09      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 2.83/3.09      inference('split', [status(esa)], ['46'])).
% 2.83/3.09  thf('134', plain,
% 2.83/3.09      (![X48 : $i, X50 : $i]:
% 2.83/3.09         ((r1_tarski @ (k1_tarski @ X48) @ X50) | ~ (r2_hidden @ X48 @ X50))),
% 2.83/3.09      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 2.83/3.09  thf('135', plain,
% 2.83/3.09      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 2.83/3.09         <= (((r2_hidden @ sk_A @ sk_B)))),
% 2.83/3.09      inference('sup-', [status(thm)], ['133', '134'])).
% 2.83/3.09  thf('136', plain, (((r2_hidden @ sk_A @ sk_B))),
% 2.83/3.09      inference('sat_resolution*', [status(thm)], ['18', '86', '127'])).
% 2.83/3.09  thf('137', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 2.83/3.09      inference('simpl_trail', [status(thm)], ['135', '136'])).
% 2.83/3.09  thf('138', plain, (((k1_ordinal1 @ sk_A) = (sk_B))),
% 2.83/3.09      inference('demod', [status(thm)], ['132', '137'])).
% 2.83/3.09  thf('139', plain, (~ (r1_ordinal1 @ sk_B @ sk_B)),
% 2.83/3.09      inference('demod', [status(thm)], ['88', '138'])).
% 2.83/3.09  thf('140', plain, (~ (v3_ordinal1 @ sk_B)),
% 2.83/3.09      inference('sup-', [status(thm)], ['15', '139'])).
% 2.83/3.09  thf('141', plain, ((v3_ordinal1 @ sk_B)),
% 2.83/3.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.83/3.09  thf('142', plain, ($false), inference('demod', [status(thm)], ['140', '141'])).
% 2.83/3.09  
% 2.83/3.09  % SZS output end Refutation
% 2.83/3.09  
% 2.97/3.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
