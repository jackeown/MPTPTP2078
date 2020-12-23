%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jt4bZkF4aB

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:33 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 131 expanded)
%              Number of leaves         :   28 (  50 expanded)
%              Depth                    :   19
%              Number of atoms          :  792 (1258 expanded)
%              Number of equality atoms :   34 (  37 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('5',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X38
        = ( k1_tarski @ X37 ) )
      | ( X38 = k1_xboole_0 )
      | ~ ( r1_tarski @ X38 @ ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('6',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

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
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','18'])).

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

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 )
      | ( X20 = X21 )
      | ( X20 = X22 )
      | ( X20 = X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
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

thf('24',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ~ ( zip_tseitin_0 @ X29 @ X25 @ X26 @ X27 )
      | ( X28
       != ( k1_enumset1 @ X27 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,(
    ! [X25: $i,X26: $i,X27: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X25 @ X26 @ X27 )
      | ~ ( r2_hidden @ X29 @ ( k1_enumset1 @ X27 @ X26 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('46',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('47',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    r2_hidden @ sk_D_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['43','56'])).

thf('58',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','57'])).

thf('59',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('60',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('61',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k3_xboole_0 @ X6 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('62',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('64',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('65',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','66'])).

thf('68',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('69',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['0','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jt4bZkF4aB
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.05/2.28  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.05/2.28  % Solved by: fo/fo7.sh
% 2.05/2.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.05/2.28  % done 2851 iterations in 1.828s
% 2.05/2.28  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.05/2.28  % SZS output start Refutation
% 2.05/2.28  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.05/2.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.05/2.28  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.05/2.28  thf(sk_A_type, type, sk_A: $i).
% 2.05/2.28  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.05/2.28  thf(sk_B_type, type, sk_B: $i).
% 2.05/2.28  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 2.05/2.28  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.05/2.28  thf(sk_D_1_type, type, sk_D_1: $i).
% 2.05/2.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.05/2.28  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.05/2.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.05/2.28  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.05/2.28  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.05/2.28  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.05/2.28  thf(t149_zfmisc_1, conjecture,
% 2.05/2.28    (![A:$i,B:$i,C:$i,D:$i]:
% 2.05/2.28     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.05/2.28         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.05/2.28       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.05/2.28  thf(zf_stmt_0, negated_conjecture,
% 2.05/2.28    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.05/2.28        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.05/2.28            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.05/2.28          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 2.05/2.28    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 2.05/2.28  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf(symmetry_r1_xboole_0, axiom,
% 2.05/2.28    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.05/2.28  thf('2', plain,
% 2.05/2.28      (![X9 : $i, X10 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X9 @ X10) | ~ (r1_xboole_0 @ X10 @ X9))),
% 2.05/2.28      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.05/2.28  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 2.05/2.28      inference('sup-', [status(thm)], ['1', '2'])).
% 2.05/2.28  thf('4', plain,
% 2.05/2.28      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf(l3_zfmisc_1, axiom,
% 2.05/2.28    (![A:$i,B:$i]:
% 2.05/2.28     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 2.05/2.28       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 2.05/2.28  thf('5', plain,
% 2.05/2.28      (![X37 : $i, X38 : $i]:
% 2.05/2.28         (((X38) = (k1_tarski @ X37))
% 2.05/2.28          | ((X38) = (k1_xboole_0))
% 2.05/2.28          | ~ (r1_tarski @ X38 @ (k1_tarski @ X37)))),
% 2.05/2.28      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 2.05/2.28  thf('6', plain,
% 2.05/2.28      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))
% 2.05/2.28        | ((k3_xboole_0 @ sk_A @ sk_B) = (k1_tarski @ sk_D_1)))),
% 2.05/2.28      inference('sup-', [status(thm)], ['4', '5'])).
% 2.05/2.28  thf(t3_xboole_0, axiom,
% 2.05/2.28    (![A:$i,B:$i]:
% 2.05/2.28     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 2.05/2.28            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.05/2.28       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.05/2.28            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.05/2.28  thf('7', plain,
% 2.05/2.28      (![X11 : $i, X12 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X12))),
% 2.05/2.28      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.05/2.28  thf('8', plain,
% 2.05/2.28      (![X11 : $i, X12 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X11))),
% 2.05/2.28      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.05/2.28  thf(d4_xboole_0, axiom,
% 2.05/2.28    (![A:$i,B:$i,C:$i]:
% 2.05/2.28     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 2.05/2.28       ( ![D:$i]:
% 2.05/2.28         ( ( r2_hidden @ D @ C ) <=>
% 2.05/2.28           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.05/2.28  thf('9', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.05/2.28         (~ (r2_hidden @ X0 @ X1)
% 2.05/2.28          | ~ (r2_hidden @ X0 @ X2)
% 2.05/2.28          | (r2_hidden @ X0 @ X3)
% 2.05/2.28          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 2.05/2.28      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.05/2.28  thf('10', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.28         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 2.05/2.28          | ~ (r2_hidden @ X0 @ X2)
% 2.05/2.28          | ~ (r2_hidden @ X0 @ X1))),
% 2.05/2.28      inference('simplify', [status(thm)], ['9'])).
% 2.05/2.28  thf('11', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X0 @ X1)
% 2.05/2.28          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 2.05/2.28          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X0)))),
% 2.05/2.28      inference('sup-', [status(thm)], ['8', '10'])).
% 2.05/2.28  thf('12', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X1 @ X0)
% 2.05/2.28          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 2.05/2.28          | (r1_xboole_0 @ X1 @ X0))),
% 2.05/2.28      inference('sup-', [status(thm)], ['7', '11'])).
% 2.05/2.28  thf('13', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((r2_hidden @ (sk_C @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 2.05/2.28          | (r1_xboole_0 @ X1 @ X0))),
% 2.05/2.28      inference('simplify', [status(thm)], ['12'])).
% 2.05/2.28  thf('14', plain,
% 2.05/2.28      (![X11 : $i, X12 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X11))),
% 2.05/2.28      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.05/2.28  thf('15', plain,
% 2.05/2.28      (![X11 : $i, X13 : $i, X14 : $i]:
% 2.05/2.28         (~ (r2_hidden @ X13 @ X11)
% 2.05/2.28          | ~ (r2_hidden @ X13 @ X14)
% 2.05/2.28          | ~ (r1_xboole_0 @ X11 @ X14))),
% 2.05/2.28      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.05/2.28  thf('16', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X0 @ X1)
% 2.05/2.28          | ~ (r1_xboole_0 @ X0 @ X2)
% 2.05/2.28          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 2.05/2.28      inference('sup-', [status(thm)], ['14', '15'])).
% 2.05/2.28  thf('17', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X0 @ X1)
% 2.05/2.28          | ~ (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 2.05/2.28          | (r1_xboole_0 @ X0 @ X1))),
% 2.05/2.28      inference('sup-', [status(thm)], ['13', '16'])).
% 2.05/2.28  thf('18', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         (~ (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 2.05/2.28          | (r1_xboole_0 @ X0 @ X1))),
% 2.05/2.28      inference('simplify', [status(thm)], ['17'])).
% 2.05/2.28  thf('19', plain,
% 2.05/2.28      ((~ (r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1))
% 2.05/2.28        | ((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))
% 2.05/2.28        | (r1_xboole_0 @ sk_B @ sk_A))),
% 2.05/2.28      inference('sup-', [status(thm)], ['6', '18'])).
% 2.05/2.28  thf(d1_enumset1, axiom,
% 2.05/2.28    (![A:$i,B:$i,C:$i,D:$i]:
% 2.05/2.28     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.05/2.28       ( ![E:$i]:
% 2.05/2.28         ( ( r2_hidden @ E @ D ) <=>
% 2.05/2.28           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 2.05/2.28  thf(zf_stmt_1, axiom,
% 2.05/2.28    (![E:$i,C:$i,B:$i,A:$i]:
% 2.05/2.28     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 2.05/2.28       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 2.05/2.28  thf('20', plain,
% 2.05/2.28      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 2.05/2.28         ((zip_tseitin_0 @ X20 @ X21 @ X22 @ X23)
% 2.05/2.28          | ((X20) = (X21))
% 2.05/2.28          | ((X20) = (X22))
% 2.05/2.28          | ((X20) = (X23)))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.05/2.28  thf('21', plain,
% 2.05/2.28      (![X11 : $i, X12 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X11))),
% 2.05/2.28      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.05/2.28  thf(t69_enumset1, axiom,
% 2.05/2.28    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.05/2.28  thf('22', plain,
% 2.05/2.28      (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 2.05/2.28      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.05/2.28  thf(t70_enumset1, axiom,
% 2.05/2.28    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.05/2.28  thf('23', plain,
% 2.05/2.28      (![X32 : $i, X33 : $i]:
% 2.05/2.28         ((k1_enumset1 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 2.05/2.28      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.05/2.28  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 2.05/2.28  thf(zf_stmt_3, axiom,
% 2.05/2.28    (![A:$i,B:$i,C:$i,D:$i]:
% 2.05/2.28     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.05/2.28       ( ![E:$i]:
% 2.05/2.28         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 2.05/2.28  thf('24', plain,
% 2.05/2.28      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.05/2.28         (~ (r2_hidden @ X29 @ X28)
% 2.05/2.28          | ~ (zip_tseitin_0 @ X29 @ X25 @ X26 @ X27)
% 2.05/2.28          | ((X28) != (k1_enumset1 @ X27 @ X26 @ X25)))),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.05/2.28  thf('25', plain,
% 2.05/2.28      (![X25 : $i, X26 : $i, X27 : $i, X29 : $i]:
% 2.05/2.28         (~ (zip_tseitin_0 @ X29 @ X25 @ X26 @ X27)
% 2.05/2.28          | ~ (r2_hidden @ X29 @ (k1_enumset1 @ X27 @ X26 @ X25)))),
% 2.05/2.28      inference('simplify', [status(thm)], ['24'])).
% 2.05/2.28  thf('26', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.28         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.05/2.28          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 2.05/2.28      inference('sup-', [status(thm)], ['23', '25'])).
% 2.05/2.28  thf('27', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 2.05/2.28          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 2.05/2.28      inference('sup-', [status(thm)], ['22', '26'])).
% 2.05/2.28  thf('28', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 2.05/2.28          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 2.05/2.28      inference('sup-', [status(thm)], ['21', '27'])).
% 2.05/2.28  thf('29', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 2.05/2.28          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 2.05/2.28          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 2.05/2.28          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 2.05/2.28      inference('sup-', [status(thm)], ['20', '28'])).
% 2.05/2.28  thf('30', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 2.05/2.28          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 2.05/2.28      inference('simplify', [status(thm)], ['29'])).
% 2.05/2.28  thf('31', plain,
% 2.05/2.28      (![X11 : $i, X12 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X12))),
% 2.05/2.28      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.05/2.28  thf('32', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((r2_hidden @ X0 @ X1)
% 2.05/2.28          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 2.05/2.28          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 2.05/2.28      inference('sup+', [status(thm)], ['30', '31'])).
% 2.05/2.28  thf('33', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 2.05/2.28      inference('simplify', [status(thm)], ['32'])).
% 2.05/2.28  thf('34', plain,
% 2.05/2.28      (![X11 : $i, X12 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X11))),
% 2.05/2.28      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.05/2.28  thf('35', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X0 @ X1)
% 2.05/2.28          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 2.05/2.28          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X0)))),
% 2.05/2.28      inference('sup-', [status(thm)], ['8', '10'])).
% 2.05/2.28  thf('36', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X0 @ X1)
% 2.05/2.28          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 2.05/2.28          | (r1_xboole_0 @ X0 @ X1))),
% 2.05/2.28      inference('sup-', [status(thm)], ['34', '35'])).
% 2.05/2.28  thf('37', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 2.05/2.28          | (r1_xboole_0 @ X0 @ X1))),
% 2.05/2.28      inference('simplify', [status(thm)], ['36'])).
% 2.05/2.28  thf('38', plain,
% 2.05/2.28      (![X11 : $i, X12 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X12))),
% 2.05/2.28      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.05/2.28  thf('39', plain,
% 2.05/2.28      (![X11 : $i, X13 : $i, X14 : $i]:
% 2.05/2.28         (~ (r2_hidden @ X13 @ X11)
% 2.05/2.28          | ~ (r2_hidden @ X13 @ X14)
% 2.05/2.28          | ~ (r1_xboole_0 @ X11 @ X14))),
% 2.05/2.28      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.05/2.28  thf('40', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X1 @ X0)
% 2.05/2.28          | ~ (r1_xboole_0 @ X0 @ X2)
% 2.05/2.28          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 2.05/2.28      inference('sup-', [status(thm)], ['38', '39'])).
% 2.05/2.28  thf('41', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X0 @ X1)
% 2.05/2.28          | ~ (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0))
% 2.05/2.28          | (r1_xboole_0 @ X0 @ X1))),
% 2.05/2.28      inference('sup-', [status(thm)], ['37', '40'])).
% 2.05/2.28  thf('42', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         (~ (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0))
% 2.05/2.28          | (r1_xboole_0 @ X0 @ X1))),
% 2.05/2.28      inference('simplify', [status(thm)], ['41'])).
% 2.05/2.28  thf('43', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i]:
% 2.05/2.28         ((r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ X0))
% 2.05/2.28          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 2.05/2.28      inference('sup-', [status(thm)], ['33', '42'])).
% 2.05/2.28  thf('44', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('45', plain,
% 2.05/2.28      (![X11 : $i, X12 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X12))),
% 2.05/2.28      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.05/2.28  thf('46', plain,
% 2.05/2.28      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.05/2.28         (~ (r2_hidden @ X4 @ X3)
% 2.05/2.28          | (r2_hidden @ X4 @ X2)
% 2.05/2.28          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 2.05/2.28      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.05/2.28  thf('47', plain,
% 2.05/2.28      (![X1 : $i, X2 : $i, X4 : $i]:
% 2.05/2.28         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 2.05/2.28      inference('simplify', [status(thm)], ['46'])).
% 2.05/2.28  thf('48', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.05/2.28          | (r2_hidden @ (sk_C @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 2.05/2.28      inference('sup-', [status(thm)], ['45', '47'])).
% 2.05/2.28  thf('49', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X0 @ X1)
% 2.05/2.28          | ~ (r1_xboole_0 @ X0 @ X2)
% 2.05/2.28          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 2.05/2.28      inference('sup-', [status(thm)], ['14', '15'])).
% 2.05/2.28  thf('50', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0))
% 2.05/2.28          | ~ (r1_xboole_0 @ X1 @ X0)
% 2.05/2.28          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))),
% 2.05/2.28      inference('sup-', [status(thm)], ['48', '49'])).
% 2.05/2.28  thf('51', plain,
% 2.05/2.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.28         (~ (r1_xboole_0 @ X1 @ X0)
% 2.05/2.28          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))),
% 2.05/2.28      inference('simplify', [status(thm)], ['50'])).
% 2.05/2.28  thf('52', plain,
% 2.05/2.28      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B))),
% 2.05/2.28      inference('sup-', [status(thm)], ['44', '51'])).
% 2.05/2.28  thf('53', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 2.05/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.28  thf('54', plain,
% 2.05/2.28      (![X11 : $i, X13 : $i, X14 : $i]:
% 2.05/2.28         (~ (r2_hidden @ X13 @ X11)
% 2.05/2.28          | ~ (r2_hidden @ X13 @ X14)
% 2.05/2.28          | ~ (r1_xboole_0 @ X11 @ X14))),
% 2.05/2.28      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.05/2.28  thf('55', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D_1 @ X0))),
% 2.05/2.28      inference('sup-', [status(thm)], ['53', '54'])).
% 2.05/2.28  thf('56', plain,
% 2.05/2.28      (![X0 : $i]: ~ (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ X0 @ sk_B))),
% 2.05/2.28      inference('sup-', [status(thm)], ['52', '55'])).
% 2.05/2.28  thf('57', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1))),
% 2.05/2.28      inference('sup-', [status(thm)], ['43', '56'])).
% 2.05/2.28  thf('58', plain,
% 2.05/2.28      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))
% 2.05/2.28        | (r1_xboole_0 @ sk_B @ sk_A))),
% 2.05/2.28      inference('demod', [status(thm)], ['19', '57'])).
% 2.05/2.28  thf('59', plain,
% 2.05/2.28      (![X9 : $i, X10 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X9 @ X10) | ~ (r1_xboole_0 @ X10 @ X9))),
% 2.05/2.28      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.05/2.28  thf('60', plain,
% 2.05/2.28      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))
% 2.05/2.28        | (r1_xboole_0 @ sk_A @ sk_B))),
% 2.05/2.28      inference('sup-', [status(thm)], ['58', '59'])).
% 2.05/2.28  thf(d7_xboole_0, axiom,
% 2.05/2.28    (![A:$i,B:$i]:
% 2.05/2.28     ( ( r1_xboole_0 @ A @ B ) <=>
% 2.05/2.28       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 2.05/2.28  thf('61', plain,
% 2.05/2.28      (![X6 : $i, X8 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X6 @ X8) | ((k3_xboole_0 @ X6 @ X8) != (k1_xboole_0)))),
% 2.05/2.28      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.05/2.28  thf('62', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 2.05/2.28      inference('clc', [status(thm)], ['60', '61'])).
% 2.05/2.28  thf('63', plain,
% 2.05/2.28      (![X9 : $i, X10 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X9 @ X10) | ~ (r1_xboole_0 @ X10 @ X9))),
% 2.05/2.28      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.05/2.28  thf('64', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 2.05/2.28      inference('sup-', [status(thm)], ['62', '63'])).
% 2.05/2.28  thf(t70_xboole_1, axiom,
% 2.05/2.28    (![A:$i,B:$i,C:$i]:
% 2.05/2.28     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 2.05/2.28            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 2.05/2.28       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 2.05/2.28            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 2.05/2.28  thf('65', plain,
% 2.05/2.28      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 2.05/2.28          | ~ (r1_xboole_0 @ X15 @ X16)
% 2.05/2.28          | ~ (r1_xboole_0 @ X15 @ X17))),
% 2.05/2.28      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.05/2.28  thf('66', plain,
% 2.05/2.28      (![X0 : $i]:
% 2.05/2.28         (~ (r1_xboole_0 @ sk_B @ X0)
% 2.05/2.28          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 2.05/2.28      inference('sup-', [status(thm)], ['64', '65'])).
% 2.05/2.28  thf('67', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 2.05/2.28      inference('sup-', [status(thm)], ['3', '66'])).
% 2.05/2.28  thf('68', plain,
% 2.05/2.28      (![X9 : $i, X10 : $i]:
% 2.05/2.28         ((r1_xboole_0 @ X9 @ X10) | ~ (r1_xboole_0 @ X10 @ X9))),
% 2.05/2.28      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.05/2.28  thf('69', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 2.05/2.28      inference('sup-', [status(thm)], ['67', '68'])).
% 2.05/2.28  thf('70', plain, ($false), inference('demod', [status(thm)], ['0', '69'])).
% 2.05/2.28  
% 2.05/2.28  % SZS output end Refutation
% 2.05/2.28  
% 2.05/2.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
