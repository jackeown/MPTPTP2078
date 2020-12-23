%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t5legp3Tt2

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:35 EST 2020

% Result     : Theorem 8.84s
% Output     : Refutation 8.84s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 295 expanded)
%              Number of leaves         :   27 (  94 expanded)
%              Depth                    :   17
%              Number of atoms          :  775 (3076 expanded)
%              Number of equality atoms :   58 ( 237 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t72_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
      <=> ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t72_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_C_2 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_C_2 )
   <= ~ ( r2_hidden @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_2 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_2 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
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

thf('5',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 )
      | ( r2_hidden @ X31 @ X35 )
      | ( X35
       != ( k1_enumset1 @ X34 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ X31 @ ( k1_enumset1 @ X34 @ X33 @ X32 ) )
      | ( zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X27 != X26 )
      | ~ ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ~ ( zip_tseitin_0 @ X26 @ X28 @ X29 @ X26 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('13',plain,
    ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k3_xboole_0 @ X16 @ X19 ) )
      | ~ ( r1_xboole_0 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,
    ( ( ( k3_xboole_0 @ sk_C_2 @ ( k2_tarski @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ sk_C_2 @ ( k2_tarski @ sk_A @ sk_B_1 ) )
      = ( k5_xboole_0 @ sk_C_2 @ k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ sk_C_2 @ ( k2_tarski @ sk_A @ sk_B_1 ) )
      = sk_C_2 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('25',plain,
    ( ( r1_xboole_0 @ sk_C_2 @ ( k2_tarski @ sk_A @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C_2 )
    | ( r2_hidden @ sk_A @ sk_C_2 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
     != ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
   <= ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['26'])).

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

thf('28',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_tarski @ sk_A @ sk_B_1 ) )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
        = ( k2_tarski @ sk_A @ sk_B_1 ) )
      & ( r2_hidden @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_2 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
     != ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('33',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X27 != X28 )
      | ~ ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ~ ( zip_tseitin_0 @ X28 @ X28 @ X29 @ X26 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ( r1_xboole_0 @ sk_C_2 @ ( k2_tarski @ sk_A @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('37',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C_2 )
   <= ( r2_hidden @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['26'])).

thf('38',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
        | ~ ( r2_hidden @ sk_B_1 @ X0 ) )
   <= ( r2_hidden @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_B_1 ) )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
        = ( k2_tarski @ sk_A @ sk_B_1 ) )
      & ( r2_hidden @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_C_2 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
     != ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
     != ( k2_tarski @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ sk_B_1 @ sk_C_2 )
    | ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['26'])).

thf('43',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_C_2 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
      = ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,(
    ~ ( r2_hidden @ sk_B_1 @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['3','31','41','42','43'])).

thf('45',plain,(
    ~ ( r2_hidden @ sk_B_1 @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['1','44'])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('46',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( r2_hidden @ X65 @ X66 )
      | ( r1_xboole_0 @ ( k2_tarski @ X65 @ X67 ) @ X66 )
      | ( r2_hidden @ X67 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = ( k5_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = ( k2_tarski @ X2 @ X1 ) )
      | ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
     != ( k2_tarski @ sk_A @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
     != ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['26'])).

thf('54',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
 != ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','31','41','42'])).

thf('55',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_2 )
 != ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B_1 )
     != ( k2_tarski @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ sk_B_1 @ sk_C_2 )
    | ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
    | ( r2_hidden @ sk_B_1 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_2 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('59',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['3','31'])).

thf('60',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['58','59'])).

thf('61',plain,(
    r2_hidden @ sk_B_1 @ sk_C_2 ),
    inference(clc,[status(thm)],['57','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['45','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t5legp3Tt2
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 8.84/9.02  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.84/9.02  % Solved by: fo/fo7.sh
% 8.84/9.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.84/9.02  % done 11317 iterations in 8.567s
% 8.84/9.02  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.84/9.02  % SZS output start Refutation
% 8.84/9.02  thf(sk_B_type, type, sk_B: $i > $i).
% 8.84/9.02  thf(sk_C_2_type, type, sk_C_2: $i).
% 8.84/9.02  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.84/9.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.84/9.02  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 8.84/9.02  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.84/9.02  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 8.84/9.02  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 8.84/9.02  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 8.84/9.02  thf(sk_A_type, type, sk_A: $i).
% 8.84/9.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.84/9.02  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 8.84/9.02  thf(sk_B_1_type, type, sk_B_1: $i).
% 8.84/9.02  thf(t72_zfmisc_1, conjecture,
% 8.84/9.02    (![A:$i,B:$i,C:$i]:
% 8.84/9.02     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 8.84/9.02       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 8.84/9.02  thf(zf_stmt_0, negated_conjecture,
% 8.84/9.02    (~( ![A:$i,B:$i,C:$i]:
% 8.84/9.02        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 8.84/9.02          ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ) )),
% 8.84/9.02    inference('cnf.neg', [status(esa)], [t72_zfmisc_1])).
% 8.84/9.02  thf('0', plain,
% 8.84/9.02      ((~ (r2_hidden @ sk_B_1 @ sk_C_2)
% 8.84/9.02        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02            = (k2_tarski @ sk_A @ sk_B_1)))),
% 8.84/9.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.84/9.02  thf('1', plain,
% 8.84/9.02      ((~ (r2_hidden @ sk_B_1 @ sk_C_2)) <= (~ ((r2_hidden @ sk_B_1 @ sk_C_2)))),
% 8.84/9.02      inference('split', [status(esa)], ['0'])).
% 8.84/9.02  thf('2', plain,
% 8.84/9.02      ((~ (r2_hidden @ sk_A @ sk_C_2)
% 8.84/9.02        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02            = (k2_tarski @ sk_A @ sk_B_1)))),
% 8.84/9.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.84/9.02  thf('3', plain,
% 8.84/9.02      (~ ((r2_hidden @ sk_A @ sk_C_2)) | 
% 8.84/9.02       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02          = (k2_tarski @ sk_A @ sk_B_1)))),
% 8.84/9.02      inference('split', [status(esa)], ['2'])).
% 8.84/9.02  thf(t70_enumset1, axiom,
% 8.84/9.02    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 8.84/9.02  thf('4', plain,
% 8.84/9.02      (![X38 : $i, X39 : $i]:
% 8.84/9.02         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 8.84/9.02      inference('cnf', [status(esa)], [t70_enumset1])).
% 8.84/9.02  thf(d1_enumset1, axiom,
% 8.84/9.02    (![A:$i,B:$i,C:$i,D:$i]:
% 8.84/9.02     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 8.84/9.02       ( ![E:$i]:
% 8.84/9.02         ( ( r2_hidden @ E @ D ) <=>
% 8.84/9.02           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 8.84/9.02  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 8.84/9.02  thf(zf_stmt_2, axiom,
% 8.84/9.02    (![E:$i,C:$i,B:$i,A:$i]:
% 8.84/9.02     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 8.84/9.02       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 8.84/9.02  thf(zf_stmt_3, axiom,
% 8.84/9.02    (![A:$i,B:$i,C:$i,D:$i]:
% 8.84/9.02     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 8.84/9.02       ( ![E:$i]:
% 8.84/9.02         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 8.84/9.02  thf('5', plain,
% 8.84/9.02      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 8.84/9.02         ((zip_tseitin_0 @ X31 @ X32 @ X33 @ X34)
% 8.84/9.02          | (r2_hidden @ X31 @ X35)
% 8.84/9.02          | ((X35) != (k1_enumset1 @ X34 @ X33 @ X32)))),
% 8.84/9.02      inference('cnf', [status(esa)], [zf_stmt_3])).
% 8.84/9.02  thf('6', plain,
% 8.84/9.02      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 8.84/9.02         ((r2_hidden @ X31 @ (k1_enumset1 @ X34 @ X33 @ X32))
% 8.84/9.02          | (zip_tseitin_0 @ X31 @ X32 @ X33 @ X34))),
% 8.84/9.02      inference('simplify', [status(thm)], ['5'])).
% 8.84/9.02  thf('7', plain,
% 8.84/9.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.84/9.02         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 8.84/9.02          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 8.84/9.02      inference('sup+', [status(thm)], ['4', '6'])).
% 8.84/9.02  thf('8', plain,
% 8.84/9.02      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 8.84/9.02         (((X27) != (X26)) | ~ (zip_tseitin_0 @ X27 @ X28 @ X29 @ X26))),
% 8.84/9.02      inference('cnf', [status(esa)], [zf_stmt_2])).
% 8.84/9.02  thf('9', plain,
% 8.84/9.02      (![X26 : $i, X28 : $i, X29 : $i]:
% 8.84/9.02         ~ (zip_tseitin_0 @ X26 @ X28 @ X29 @ X26)),
% 8.84/9.02      inference('simplify', [status(thm)], ['8'])).
% 8.84/9.02  thf('10', plain,
% 8.84/9.02      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 8.84/9.02      inference('sup-', [status(thm)], ['7', '9'])).
% 8.84/9.02  thf('11', plain,
% 8.84/9.02      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02          = (k2_tarski @ sk_A @ sk_B_1)))
% 8.84/9.02         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02                = (k2_tarski @ sk_A @ sk_B_1))))),
% 8.84/9.02      inference('split', [status(esa)], ['2'])).
% 8.84/9.02  thf(t79_xboole_1, axiom,
% 8.84/9.02    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 8.84/9.02  thf('12', plain,
% 8.84/9.02      (![X24 : $i, X25 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ X25)),
% 8.84/9.02      inference('cnf', [status(esa)], [t79_xboole_1])).
% 8.84/9.02  thf('13', plain,
% 8.84/9.02      (((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2))
% 8.84/9.02         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02                = (k2_tarski @ sk_A @ sk_B_1))))),
% 8.84/9.02      inference('sup+', [status(thm)], ['11', '12'])).
% 8.84/9.02  thf(t7_xboole_0, axiom,
% 8.84/9.02    (![A:$i]:
% 8.84/9.02     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 8.84/9.02          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 8.84/9.02  thf('14', plain,
% 8.84/9.02      (![X20 : $i]:
% 8.84/9.02         (((X20) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X20) @ X20))),
% 8.84/9.02      inference('cnf', [status(esa)], [t7_xboole_0])).
% 8.84/9.02  thf(t4_xboole_0, axiom,
% 8.84/9.02    (![A:$i,B:$i]:
% 8.84/9.02     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 8.84/9.02            ( r1_xboole_0 @ A @ B ) ) ) & 
% 8.84/9.02       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 8.84/9.02            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 8.84/9.02  thf('15', plain,
% 8.84/9.02      (![X16 : $i, X18 : $i, X19 : $i]:
% 8.84/9.02         (~ (r2_hidden @ X18 @ (k3_xboole_0 @ X16 @ X19))
% 8.84/9.02          | ~ (r1_xboole_0 @ X16 @ X19))),
% 8.84/9.02      inference('cnf', [status(esa)], [t4_xboole_0])).
% 8.84/9.02  thf('16', plain,
% 8.84/9.02      (![X0 : $i, X1 : $i]:
% 8.84/9.02         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 8.84/9.02      inference('sup-', [status(thm)], ['14', '15'])).
% 8.84/9.02  thf('17', plain,
% 8.84/9.02      ((((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2) = (k1_xboole_0)))
% 8.84/9.02         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02                = (k2_tarski @ sk_A @ sk_B_1))))),
% 8.84/9.02      inference('sup-', [status(thm)], ['13', '16'])).
% 8.84/9.02  thf(commutativity_k3_xboole_0, axiom,
% 8.84/9.02    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 8.84/9.02  thf('18', plain,
% 8.84/9.02      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.84/9.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.84/9.02  thf('19', plain,
% 8.84/9.02      ((((k3_xboole_0 @ sk_C_2 @ (k2_tarski @ sk_A @ sk_B_1)) = (k1_xboole_0)))
% 8.84/9.02         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02                = (k2_tarski @ sk_A @ sk_B_1))))),
% 8.84/9.02      inference('demod', [status(thm)], ['17', '18'])).
% 8.84/9.02  thf(t100_xboole_1, axiom,
% 8.84/9.02    (![A:$i,B:$i]:
% 8.84/9.02     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 8.84/9.02  thf('20', plain,
% 8.84/9.02      (![X21 : $i, X22 : $i]:
% 8.84/9.02         ((k4_xboole_0 @ X21 @ X22)
% 8.84/9.02           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 8.84/9.02      inference('cnf', [status(esa)], [t100_xboole_1])).
% 8.84/9.02  thf('21', plain,
% 8.84/9.02      ((((k4_xboole_0 @ sk_C_2 @ (k2_tarski @ sk_A @ sk_B_1))
% 8.84/9.02          = (k5_xboole_0 @ sk_C_2 @ k1_xboole_0)))
% 8.84/9.02         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02                = (k2_tarski @ sk_A @ sk_B_1))))),
% 8.84/9.02      inference('sup+', [status(thm)], ['19', '20'])).
% 8.84/9.02  thf(t5_boole, axiom,
% 8.84/9.02    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 8.84/9.02  thf('22', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 8.84/9.02      inference('cnf', [status(esa)], [t5_boole])).
% 8.84/9.02  thf('23', plain,
% 8.84/9.02      ((((k4_xboole_0 @ sk_C_2 @ (k2_tarski @ sk_A @ sk_B_1)) = (sk_C_2)))
% 8.84/9.02         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02                = (k2_tarski @ sk_A @ sk_B_1))))),
% 8.84/9.02      inference('demod', [status(thm)], ['21', '22'])).
% 8.84/9.02  thf('24', plain,
% 8.84/9.02      (![X24 : $i, X25 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ X25)),
% 8.84/9.02      inference('cnf', [status(esa)], [t79_xboole_1])).
% 8.84/9.02  thf('25', plain,
% 8.84/9.02      (((r1_xboole_0 @ sk_C_2 @ (k2_tarski @ sk_A @ sk_B_1)))
% 8.84/9.02         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02                = (k2_tarski @ sk_A @ sk_B_1))))),
% 8.84/9.02      inference('sup+', [status(thm)], ['23', '24'])).
% 8.84/9.02  thf('26', plain,
% 8.84/9.02      (((r2_hidden @ sk_B_1 @ sk_C_2)
% 8.84/9.02        | (r2_hidden @ sk_A @ sk_C_2)
% 8.84/9.02        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02            != (k2_tarski @ sk_A @ sk_B_1)))),
% 8.84/9.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.84/9.02  thf('27', plain,
% 8.84/9.02      (((r2_hidden @ sk_A @ sk_C_2)) <= (((r2_hidden @ sk_A @ sk_C_2)))),
% 8.84/9.02      inference('split', [status(esa)], ['26'])).
% 8.84/9.02  thf(t3_xboole_0, axiom,
% 8.84/9.02    (![A:$i,B:$i]:
% 8.84/9.02     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 8.84/9.02            ( r1_xboole_0 @ A @ B ) ) ) & 
% 8.84/9.02       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 8.84/9.02            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 8.84/9.02  thf('28', plain,
% 8.84/9.02      (![X12 : $i, X14 : $i, X15 : $i]:
% 8.84/9.02         (~ (r2_hidden @ X14 @ X12)
% 8.84/9.02          | ~ (r2_hidden @ X14 @ X15)
% 8.84/9.02          | ~ (r1_xboole_0 @ X12 @ X15))),
% 8.84/9.02      inference('cnf', [status(esa)], [t3_xboole_0])).
% 8.84/9.02  thf('29', plain,
% 8.84/9.02      ((![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_A @ X0)))
% 8.84/9.02         <= (((r2_hidden @ sk_A @ sk_C_2)))),
% 8.84/9.02      inference('sup-', [status(thm)], ['27', '28'])).
% 8.84/9.02  thf('30', plain,
% 8.84/9.02      ((~ (r2_hidden @ sk_A @ (k2_tarski @ sk_A @ sk_B_1)))
% 8.84/9.02         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02                = (k2_tarski @ sk_A @ sk_B_1))) & 
% 8.84/9.02             ((r2_hidden @ sk_A @ sk_C_2)))),
% 8.84/9.02      inference('sup-', [status(thm)], ['25', '29'])).
% 8.84/9.02  thf('31', plain,
% 8.84/9.02      (~ ((r2_hidden @ sk_A @ sk_C_2)) | 
% 8.84/9.02       ~
% 8.84/9.02       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02          = (k2_tarski @ sk_A @ sk_B_1)))),
% 8.84/9.02      inference('sup-', [status(thm)], ['10', '30'])).
% 8.84/9.02  thf('32', plain,
% 8.84/9.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.84/9.02         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 8.84/9.02          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 8.84/9.02      inference('sup+', [status(thm)], ['4', '6'])).
% 8.84/9.02  thf('33', plain,
% 8.84/9.02      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 8.84/9.02         (((X27) != (X28)) | ~ (zip_tseitin_0 @ X27 @ X28 @ X29 @ X26))),
% 8.84/9.02      inference('cnf', [status(esa)], [zf_stmt_2])).
% 8.84/9.02  thf('34', plain,
% 8.84/9.02      (![X26 : $i, X28 : $i, X29 : $i]:
% 8.84/9.02         ~ (zip_tseitin_0 @ X28 @ X28 @ X29 @ X26)),
% 8.84/9.02      inference('simplify', [status(thm)], ['33'])).
% 8.84/9.02  thf('35', plain,
% 8.84/9.02      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 8.84/9.02      inference('sup-', [status(thm)], ['32', '34'])).
% 8.84/9.02  thf('36', plain,
% 8.84/9.02      (((r1_xboole_0 @ sk_C_2 @ (k2_tarski @ sk_A @ sk_B_1)))
% 8.84/9.02         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02                = (k2_tarski @ sk_A @ sk_B_1))))),
% 8.84/9.02      inference('sup+', [status(thm)], ['23', '24'])).
% 8.84/9.02  thf('37', plain,
% 8.84/9.02      (((r2_hidden @ sk_B_1 @ sk_C_2)) <= (((r2_hidden @ sk_B_1 @ sk_C_2)))),
% 8.84/9.02      inference('split', [status(esa)], ['26'])).
% 8.84/9.02  thf('38', plain,
% 8.84/9.02      (![X12 : $i, X14 : $i, X15 : $i]:
% 8.84/9.02         (~ (r2_hidden @ X14 @ X12)
% 8.84/9.02          | ~ (r2_hidden @ X14 @ X15)
% 8.84/9.02          | ~ (r1_xboole_0 @ X12 @ X15))),
% 8.84/9.02      inference('cnf', [status(esa)], [t3_xboole_0])).
% 8.84/9.02  thf('39', plain,
% 8.84/9.02      ((![X0 : $i]:
% 8.84/9.02          (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_B_1 @ X0)))
% 8.84/9.02         <= (((r2_hidden @ sk_B_1 @ sk_C_2)))),
% 8.84/9.02      inference('sup-', [status(thm)], ['37', '38'])).
% 8.84/9.02  thf('40', plain,
% 8.84/9.02      ((~ (r2_hidden @ sk_B_1 @ (k2_tarski @ sk_A @ sk_B_1)))
% 8.84/9.02         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02                = (k2_tarski @ sk_A @ sk_B_1))) & 
% 8.84/9.02             ((r2_hidden @ sk_B_1 @ sk_C_2)))),
% 8.84/9.02      inference('sup-', [status(thm)], ['36', '39'])).
% 8.84/9.02  thf('41', plain,
% 8.84/9.02      (~ ((r2_hidden @ sk_B_1 @ sk_C_2)) | 
% 8.84/9.02       ~
% 8.84/9.02       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02          = (k2_tarski @ sk_A @ sk_B_1)))),
% 8.84/9.02      inference('sup-', [status(thm)], ['35', '40'])).
% 8.84/9.02  thf('42', plain,
% 8.84/9.02      (~
% 8.84/9.02       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02          = (k2_tarski @ sk_A @ sk_B_1))) | 
% 8.84/9.02       ((r2_hidden @ sk_B_1 @ sk_C_2)) | ((r2_hidden @ sk_A @ sk_C_2))),
% 8.84/9.02      inference('split', [status(esa)], ['26'])).
% 8.84/9.02  thf('43', plain,
% 8.84/9.02      (~ ((r2_hidden @ sk_B_1 @ sk_C_2)) | 
% 8.84/9.02       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02          = (k2_tarski @ sk_A @ sk_B_1)))),
% 8.84/9.02      inference('split', [status(esa)], ['0'])).
% 8.84/9.02  thf('44', plain, (~ ((r2_hidden @ sk_B_1 @ sk_C_2))),
% 8.84/9.02      inference('sat_resolution*', [status(thm)], ['3', '31', '41', '42', '43'])).
% 8.84/9.02  thf('45', plain, (~ (r2_hidden @ sk_B_1 @ sk_C_2)),
% 8.84/9.02      inference('simpl_trail', [status(thm)], ['1', '44'])).
% 8.84/9.02  thf(t57_zfmisc_1, axiom,
% 8.84/9.02    (![A:$i,B:$i,C:$i]:
% 8.84/9.02     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 8.84/9.02          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 8.84/9.02  thf('46', plain,
% 8.84/9.02      (![X65 : $i, X66 : $i, X67 : $i]:
% 8.84/9.02         ((r2_hidden @ X65 @ X66)
% 8.84/9.02          | (r1_xboole_0 @ (k2_tarski @ X65 @ X67) @ X66)
% 8.84/9.02          | (r2_hidden @ X67 @ X66))),
% 8.84/9.02      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 8.84/9.02  thf('47', plain,
% 8.84/9.02      (![X0 : $i, X1 : $i]:
% 8.84/9.02         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 8.84/9.02      inference('sup-', [status(thm)], ['14', '15'])).
% 8.84/9.02  thf('48', plain,
% 8.84/9.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.84/9.02         ((r2_hidden @ X1 @ X0)
% 8.84/9.02          | (r2_hidden @ X2 @ X0)
% 8.84/9.02          | ((k3_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) = (k1_xboole_0)))),
% 8.84/9.02      inference('sup-', [status(thm)], ['46', '47'])).
% 8.84/9.02  thf('49', plain,
% 8.84/9.02      (![X21 : $i, X22 : $i]:
% 8.84/9.02         ((k4_xboole_0 @ X21 @ X22)
% 8.84/9.02           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 8.84/9.02      inference('cnf', [status(esa)], [t100_xboole_1])).
% 8.84/9.02  thf('50', plain,
% 8.84/9.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.84/9.02         (((k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0)
% 8.84/9.02            = (k5_xboole_0 @ (k2_tarski @ X2 @ X1) @ k1_xboole_0))
% 8.84/9.02          | (r2_hidden @ X2 @ X0)
% 8.84/9.02          | (r2_hidden @ X1 @ X0))),
% 8.84/9.02      inference('sup+', [status(thm)], ['48', '49'])).
% 8.84/9.02  thf('51', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 8.84/9.02      inference('cnf', [status(esa)], [t5_boole])).
% 8.84/9.02  thf('52', plain,
% 8.84/9.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.84/9.02         (((k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) = (k2_tarski @ X2 @ X1))
% 8.84/9.02          | (r2_hidden @ X2 @ X0)
% 8.84/9.02          | (r2_hidden @ X1 @ X0))),
% 8.84/9.02      inference('demod', [status(thm)], ['50', '51'])).
% 8.84/9.02  thf('53', plain,
% 8.84/9.02      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02          != (k2_tarski @ sk_A @ sk_B_1)))
% 8.84/9.02         <= (~
% 8.84/9.02             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02                = (k2_tarski @ sk_A @ sk_B_1))))),
% 8.84/9.02      inference('split', [status(esa)], ['26'])).
% 8.84/9.02  thf('54', plain,
% 8.84/9.02      (~
% 8.84/9.02       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02          = (k2_tarski @ sk_A @ sk_B_1)))),
% 8.84/9.02      inference('sat_resolution*', [status(thm)], ['3', '31', '41', '42'])).
% 8.84/9.02  thf('55', plain,
% 8.84/9.02      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_2)
% 8.84/9.02         != (k2_tarski @ sk_A @ sk_B_1))),
% 8.84/9.02      inference('simpl_trail', [status(thm)], ['53', '54'])).
% 8.84/9.02  thf('56', plain,
% 8.84/9.02      ((((k2_tarski @ sk_A @ sk_B_1) != (k2_tarski @ sk_A @ sk_B_1))
% 8.84/9.02        | (r2_hidden @ sk_B_1 @ sk_C_2)
% 8.84/9.02        | (r2_hidden @ sk_A @ sk_C_2))),
% 8.84/9.02      inference('sup-', [status(thm)], ['52', '55'])).
% 8.84/9.02  thf('57', plain,
% 8.84/9.02      (((r2_hidden @ sk_A @ sk_C_2) | (r2_hidden @ sk_B_1 @ sk_C_2))),
% 8.84/9.02      inference('simplify', [status(thm)], ['56'])).
% 8.84/9.02  thf('58', plain,
% 8.84/9.02      ((~ (r2_hidden @ sk_A @ sk_C_2)) <= (~ ((r2_hidden @ sk_A @ sk_C_2)))),
% 8.84/9.02      inference('split', [status(esa)], ['2'])).
% 8.84/9.02  thf('59', plain, (~ ((r2_hidden @ sk_A @ sk_C_2))),
% 8.84/9.02      inference('sat_resolution*', [status(thm)], ['3', '31'])).
% 8.84/9.02  thf('60', plain, (~ (r2_hidden @ sk_A @ sk_C_2)),
% 8.84/9.02      inference('simpl_trail', [status(thm)], ['58', '59'])).
% 8.84/9.02  thf('61', plain, ((r2_hidden @ sk_B_1 @ sk_C_2)),
% 8.84/9.02      inference('clc', [status(thm)], ['57', '60'])).
% 8.84/9.02  thf('62', plain, ($false), inference('demod', [status(thm)], ['45', '61'])).
% 8.84/9.02  
% 8.84/9.02  % SZS output end Refutation
% 8.84/9.02  
% 8.84/9.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
