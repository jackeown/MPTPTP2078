%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YwQQM62VPb

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:54 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 258 expanded)
%              Number of leaves         :   29 (  85 expanded)
%              Depth                    :   18
%              Number of atoms          :  846 (2284 expanded)
%              Number of equality atoms :   74 ( 163 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('7',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
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

thf('17',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 )
      | ( r2_hidden @ X25 @ X29 )
      | ( X29
       != ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X25 @ ( k1_enumset1 @ X28 @ X27 @ X26 ) )
      | ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X21 != X20 )
      | ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ~ ( zip_tseitin_0 @ X20 @ X22 @ X23 @ X20 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','26'])).

thf('28',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','27'])).

thf('29',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','28'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( X21 = X22 )
      | ( X21 = X23 )
      | ( X21 = X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('41',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('42',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('43',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ~ ( zip_tseitin_0 @ X30 @ X26 @ X27 @ X28 )
      | ( X29
       != ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,(
    ! [X26: $i,X27: $i,X28: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X26 @ X27 @ X28 )
      | ~ ( r2_hidden @ X30 @ ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( X21 = X22 )
      | ( X21 = X23 )
      | ( X21 = X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( sk_C @ ( k1_tarski @ X0 ) @ X1 ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['49','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ k1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['38','59'])).

thf('61',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('66',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('69',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('71',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('74',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('75',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('76',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','27','75'])).

thf('77',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['74','76'])).

thf('78',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['73','77'])).

thf('79',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['29','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YwQQM62VPb
% 0.15/0.37  % Computer   : n017.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 12:13:16 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 1.02/1.20  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.02/1.20  % Solved by: fo/fo7.sh
% 1.02/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.20  % done 1418 iterations in 0.714s
% 1.02/1.20  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.02/1.20  % SZS output start Refutation
% 1.02/1.20  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.02/1.20  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.02/1.20  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.02/1.20  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.02/1.20  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.02/1.20  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.02/1.20  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.02/1.20  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.02/1.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.02/1.20  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.20  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.02/1.20  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.02/1.20  thf(sk_B_type, type, sk_B: $i).
% 1.02/1.20  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.02/1.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.02/1.20  thf(t65_zfmisc_1, conjecture,
% 1.02/1.20    (![A:$i,B:$i]:
% 1.02/1.20     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.02/1.20       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.02/1.20  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.20    (~( ![A:$i,B:$i]:
% 1.02/1.20        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.02/1.20          ( ~( r2_hidden @ B @ A ) ) ) )),
% 1.02/1.20    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 1.02/1.20  thf('0', plain,
% 1.02/1.20      ((~ (r2_hidden @ sk_B @ sk_A)
% 1.02/1.20        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('1', plain,
% 1.02/1.20      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 1.02/1.20      inference('split', [status(esa)], ['0'])).
% 1.02/1.20  thf('2', plain,
% 1.02/1.20      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 1.02/1.20       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.02/1.20      inference('split', [status(esa)], ['0'])).
% 1.02/1.20  thf('3', plain,
% 1.02/1.20      (((r2_hidden @ sk_B @ sk_A)
% 1.02/1.20        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.20  thf('4', plain,
% 1.02/1.20      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 1.02/1.20      inference('split', [status(esa)], ['3'])).
% 1.02/1.20  thf('5', plain,
% 1.02/1.20      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 1.02/1.20         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.02/1.20      inference('split', [status(esa)], ['0'])).
% 1.02/1.20  thf(t79_xboole_1, axiom,
% 1.02/1.20    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.02/1.20  thf('6', plain,
% 1.02/1.20      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 1.02/1.20      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.02/1.20  thf('7', plain,
% 1.02/1.20      (((r1_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))
% 1.02/1.20         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.02/1.20      inference('sup+', [status(thm)], ['5', '6'])).
% 1.02/1.20  thf(t3_xboole_0, axiom,
% 1.02/1.20    (![A:$i,B:$i]:
% 1.02/1.20     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.02/1.20            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.02/1.20       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.02/1.20            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.02/1.20  thf('8', plain,
% 1.02/1.20      (![X8 : $i, X9 : $i]:
% 1.02/1.20         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 1.02/1.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.02/1.20  thf('9', plain,
% 1.02/1.20      (![X8 : $i, X9 : $i]:
% 1.02/1.20         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 1.02/1.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.02/1.20  thf('10', plain,
% 1.02/1.20      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.02/1.20         (~ (r2_hidden @ X10 @ X8)
% 1.02/1.20          | ~ (r2_hidden @ X10 @ X11)
% 1.02/1.20          | ~ (r1_xboole_0 @ X8 @ X11))),
% 1.02/1.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.02/1.20  thf('11', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         ((r1_xboole_0 @ X1 @ X0)
% 1.02/1.20          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.02/1.20          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 1.02/1.20      inference('sup-', [status(thm)], ['9', '10'])).
% 1.02/1.20  thf('12', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         ((r1_xboole_0 @ X0 @ X1)
% 1.02/1.20          | ~ (r1_xboole_0 @ X1 @ X0)
% 1.02/1.20          | (r1_xboole_0 @ X0 @ X1))),
% 1.02/1.20      inference('sup-', [status(thm)], ['8', '11'])).
% 1.02/1.20  thf('13', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.02/1.20      inference('simplify', [status(thm)], ['12'])).
% 1.02/1.20  thf('14', plain,
% 1.02/1.20      (((r1_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))
% 1.02/1.20         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.02/1.20      inference('sup-', [status(thm)], ['7', '13'])).
% 1.02/1.20  thf(t69_enumset1, axiom,
% 1.02/1.20    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.02/1.20  thf('15', plain,
% 1.02/1.20      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 1.02/1.20      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.02/1.20  thf(t70_enumset1, axiom,
% 1.02/1.20    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.02/1.20  thf('16', plain,
% 1.02/1.20      (![X33 : $i, X34 : $i]:
% 1.02/1.20         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 1.02/1.20      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.02/1.20  thf(d1_enumset1, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.02/1.20     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.02/1.20       ( ![E:$i]:
% 1.02/1.20         ( ( r2_hidden @ E @ D ) <=>
% 1.02/1.20           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.02/1.20  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.02/1.20  thf(zf_stmt_2, axiom,
% 1.02/1.20    (![E:$i,C:$i,B:$i,A:$i]:
% 1.02/1.20     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.02/1.20       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.02/1.20  thf(zf_stmt_3, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.02/1.20     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.02/1.20       ( ![E:$i]:
% 1.02/1.20         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.02/1.20  thf('17', plain,
% 1.02/1.20      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.02/1.20         ((zip_tseitin_0 @ X25 @ X26 @ X27 @ X28)
% 1.02/1.20          | (r2_hidden @ X25 @ X29)
% 1.02/1.20          | ((X29) != (k1_enumset1 @ X28 @ X27 @ X26)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.02/1.20  thf('18', plain,
% 1.02/1.20      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.02/1.20         ((r2_hidden @ X25 @ (k1_enumset1 @ X28 @ X27 @ X26))
% 1.02/1.20          | (zip_tseitin_0 @ X25 @ X26 @ X27 @ X28))),
% 1.02/1.20      inference('simplify', [status(thm)], ['17'])).
% 1.02/1.20  thf('19', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.02/1.20          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.02/1.20      inference('sup+', [status(thm)], ['16', '18'])).
% 1.02/1.20  thf('20', plain,
% 1.02/1.20      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.02/1.20         (((X21) != (X20)) | ~ (zip_tseitin_0 @ X21 @ X22 @ X23 @ X20))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.02/1.20  thf('21', plain,
% 1.02/1.20      (![X20 : $i, X22 : $i, X23 : $i]:
% 1.02/1.20         ~ (zip_tseitin_0 @ X20 @ X22 @ X23 @ X20)),
% 1.02/1.20      inference('simplify', [status(thm)], ['20'])).
% 1.02/1.20  thf('22', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.02/1.20      inference('sup-', [status(thm)], ['19', '21'])).
% 1.02/1.20  thf('23', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.02/1.20      inference('sup+', [status(thm)], ['15', '22'])).
% 1.02/1.20  thf('24', plain,
% 1.02/1.20      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.02/1.20         (~ (r2_hidden @ X10 @ X8)
% 1.02/1.20          | ~ (r2_hidden @ X10 @ X11)
% 1.02/1.20          | ~ (r1_xboole_0 @ X8 @ X11))),
% 1.02/1.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.02/1.20  thf('25', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.02/1.20      inference('sup-', [status(thm)], ['23', '24'])).
% 1.02/1.20  thf('26', plain,
% 1.02/1.20      ((~ (r2_hidden @ sk_B @ sk_A))
% 1.02/1.20         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.02/1.20      inference('sup-', [status(thm)], ['14', '25'])).
% 1.02/1.20  thf('27', plain,
% 1.02/1.20      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 1.02/1.20       ~ ((r2_hidden @ sk_B @ sk_A))),
% 1.02/1.20      inference('sup-', [status(thm)], ['4', '26'])).
% 1.02/1.20  thf('28', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 1.02/1.20      inference('sat_resolution*', [status(thm)], ['2', '27'])).
% 1.02/1.20  thf('29', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 1.02/1.20      inference('simpl_trail', [status(thm)], ['1', '28'])).
% 1.02/1.20  thf(d4_xboole_0, axiom,
% 1.02/1.20    (![A:$i,B:$i,C:$i]:
% 1.02/1.20     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.02/1.20       ( ![D:$i]:
% 1.02/1.20         ( ( r2_hidden @ D @ C ) <=>
% 1.02/1.20           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.02/1.20  thf('30', plain,
% 1.02/1.20      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.02/1.20         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.02/1.20          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.02/1.20          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.02/1.20      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.02/1.20  thf(t4_boole, axiom,
% 1.02/1.20    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.02/1.20  thf('31', plain,
% 1.02/1.20      (![X15 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 1.02/1.20      inference('cnf', [status(esa)], [t4_boole])).
% 1.02/1.20  thf('32', plain,
% 1.02/1.20      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 1.02/1.20      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.02/1.20  thf('33', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.02/1.20      inference('sup+', [status(thm)], ['31', '32'])).
% 1.02/1.20  thf('34', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.02/1.20      inference('simplify', [status(thm)], ['12'])).
% 1.02/1.20  thf('35', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.02/1.20      inference('sup-', [status(thm)], ['33', '34'])).
% 1.02/1.20  thf('36', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.02/1.20      inference('sup-', [status(thm)], ['23', '24'])).
% 1.02/1.20  thf('37', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.02/1.20      inference('sup-', [status(thm)], ['35', '36'])).
% 1.02/1.20  thf('38', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 1.02/1.20          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.02/1.20      inference('sup-', [status(thm)], ['30', '37'])).
% 1.02/1.20  thf('39', plain,
% 1.02/1.20      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.02/1.20         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 1.02/1.20          | ((X21) = (X22))
% 1.02/1.20          | ((X21) = (X23))
% 1.02/1.20          | ((X21) = (X24)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.02/1.20  thf('40', plain,
% 1.02/1.20      (![X8 : $i, X9 : $i]:
% 1.02/1.20         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 1.02/1.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.02/1.20  thf('41', plain,
% 1.02/1.20      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 1.02/1.20      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.02/1.20  thf('42', plain,
% 1.02/1.20      (![X33 : $i, X34 : $i]:
% 1.02/1.20         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 1.02/1.20      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.02/1.20  thf('43', plain,
% 1.02/1.20      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.02/1.20         (~ (r2_hidden @ X30 @ X29)
% 1.02/1.20          | ~ (zip_tseitin_0 @ X30 @ X26 @ X27 @ X28)
% 1.02/1.20          | ((X29) != (k1_enumset1 @ X28 @ X27 @ X26)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.02/1.20  thf('44', plain,
% 1.02/1.20      (![X26 : $i, X27 : $i, X28 : $i, X30 : $i]:
% 1.02/1.20         (~ (zip_tseitin_0 @ X30 @ X26 @ X27 @ X28)
% 1.02/1.20          | ~ (r2_hidden @ X30 @ (k1_enumset1 @ X28 @ X27 @ X26)))),
% 1.02/1.20      inference('simplify', [status(thm)], ['43'])).
% 1.02/1.20  thf('45', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.20         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.02/1.20          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.02/1.20      inference('sup-', [status(thm)], ['42', '44'])).
% 1.02/1.20  thf('46', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.02/1.20          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.02/1.20      inference('sup-', [status(thm)], ['41', '45'])).
% 1.02/1.20  thf('47', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.02/1.20          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 1.02/1.20      inference('sup-', [status(thm)], ['40', '46'])).
% 1.02/1.20  thf('48', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.02/1.20          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.02/1.20          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.02/1.20          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.02/1.20      inference('sup-', [status(thm)], ['39', '47'])).
% 1.02/1.20  thf('49', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.02/1.20          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.02/1.20      inference('simplify', [status(thm)], ['48'])).
% 1.02/1.20  thf('50', plain,
% 1.02/1.20      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.02/1.20         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 1.02/1.20          | ((X21) = (X22))
% 1.02/1.20          | ((X21) = (X23))
% 1.02/1.20          | ((X21) = (X24)))),
% 1.02/1.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.02/1.20  thf('51', plain,
% 1.02/1.20      (![X8 : $i, X9 : $i]:
% 1.02/1.20         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 1.02/1.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.02/1.20  thf('52', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.02/1.20          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.02/1.20      inference('sup-', [status(thm)], ['41', '45'])).
% 1.02/1.20  thf('53', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 1.02/1.20          | ~ (zip_tseitin_0 @ (sk_C @ (k1_tarski @ X0) @ X1) @ X0 @ X0 @ X0))),
% 1.02/1.20      inference('sup-', [status(thm)], ['51', '52'])).
% 1.02/1.20  thf('54', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (((sk_C @ (k1_tarski @ X0) @ X1) = (X0))
% 1.02/1.20          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0))
% 1.02/1.20          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0))
% 1.02/1.20          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 1.02/1.20      inference('sup-', [status(thm)], ['50', '53'])).
% 1.02/1.20  thf('55', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 1.02/1.20          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 1.02/1.20      inference('simplify', [status(thm)], ['54'])).
% 1.02/1.20  thf('56', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (((X0) = (X1))
% 1.02/1.20          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 1.02/1.20          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.02/1.20      inference('sup+', [status(thm)], ['49', '55'])).
% 1.02/1.20  thf('57', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         ((r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 1.02/1.20      inference('simplify', [status(thm)], ['56'])).
% 1.02/1.20  thf('58', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.02/1.20      inference('sup-', [status(thm)], ['23', '24'])).
% 1.02/1.20  thf('59', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.02/1.20      inference('sup-', [status(thm)], ['57', '58'])).
% 1.02/1.20  thf('60', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.02/1.20          | ((sk_D @ k1_xboole_0 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 1.02/1.20      inference('sup-', [status(thm)], ['38', '59'])).
% 1.02/1.20  thf('61', plain,
% 1.02/1.20      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.02/1.20         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.02/1.20          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.02/1.20          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.02/1.20      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.02/1.20  thf('62', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.02/1.20      inference('sup-', [status(thm)], ['35', '36'])).
% 1.02/1.20  thf('63', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 1.02/1.20          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.02/1.20      inference('sup-', [status(thm)], ['61', '62'])).
% 1.02/1.20  thf('64', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         ((r2_hidden @ X0 @ X1)
% 1.02/1.20          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.02/1.20          | ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.02/1.20      inference('sup+', [status(thm)], ['60', '63'])).
% 1.02/1.20  thf('65', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.02/1.20          | (r2_hidden @ X0 @ X1))),
% 1.02/1.20      inference('simplify', [status(thm)], ['64'])).
% 1.02/1.20  thf(t100_xboole_1, axiom,
% 1.02/1.20    (![A:$i,B:$i]:
% 1.02/1.20     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.02/1.20  thf('66', plain,
% 1.02/1.20      (![X12 : $i, X13 : $i]:
% 1.02/1.20         ((k4_xboole_0 @ X12 @ X13)
% 1.02/1.20           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.02/1.20      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.02/1.20  thf('67', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 1.02/1.20            = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 1.02/1.20          | (r2_hidden @ X0 @ X1))),
% 1.02/1.20      inference('sup+', [status(thm)], ['65', '66'])).
% 1.02/1.20  thf('68', plain,
% 1.02/1.20      (![X15 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 1.02/1.20      inference('cnf', [status(esa)], [t4_boole])).
% 1.02/1.20  thf(t98_xboole_1, axiom,
% 1.02/1.20    (![A:$i,B:$i]:
% 1.02/1.20     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.02/1.20  thf('69', plain,
% 1.02/1.20      (![X18 : $i, X19 : $i]:
% 1.02/1.20         ((k2_xboole_0 @ X18 @ X19)
% 1.02/1.20           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 1.02/1.20      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.02/1.20  thf('70', plain,
% 1.02/1.20      (![X0 : $i]:
% 1.02/1.20         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.02/1.20      inference('sup+', [status(thm)], ['68', '69'])).
% 1.02/1.20  thf(t1_boole, axiom,
% 1.02/1.20    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.02/1.20  thf('71', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.02/1.20      inference('cnf', [status(esa)], [t1_boole])).
% 1.02/1.20  thf('72', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.02/1.20      inference('sup+', [status(thm)], ['70', '71'])).
% 1.02/1.20  thf('73', plain,
% 1.02/1.20      (![X0 : $i, X1 : $i]:
% 1.02/1.20         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 1.02/1.20          | (r2_hidden @ X0 @ X1))),
% 1.02/1.20      inference('demod', [status(thm)], ['67', '72'])).
% 1.02/1.20  thf('74', plain,
% 1.02/1.20      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 1.02/1.20         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.02/1.20      inference('split', [status(esa)], ['3'])).
% 1.02/1.20  thf('75', plain,
% 1.02/1.20      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 1.02/1.20       ((r2_hidden @ sk_B @ sk_A))),
% 1.02/1.20      inference('split', [status(esa)], ['3'])).
% 1.02/1.20  thf('76', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.02/1.20      inference('sat_resolution*', [status(thm)], ['2', '27', '75'])).
% 1.02/1.20  thf('77', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 1.02/1.20      inference('simpl_trail', [status(thm)], ['74', '76'])).
% 1.02/1.20  thf('78', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 1.02/1.20      inference('sup-', [status(thm)], ['73', '77'])).
% 1.02/1.20  thf('79', plain, ((r2_hidden @ sk_B @ sk_A)),
% 1.02/1.20      inference('simplify', [status(thm)], ['78'])).
% 1.02/1.20  thf('80', plain, ($false), inference('demod', [status(thm)], ['29', '79'])).
% 1.02/1.20  
% 1.02/1.20  % SZS output end Refutation
% 1.02/1.20  
% 1.02/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
