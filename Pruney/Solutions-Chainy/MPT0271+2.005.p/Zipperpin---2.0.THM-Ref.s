%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wrBNhls7K9

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:21 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  150 (1153 expanded)
%              Number of leaves         :   36 ( 360 expanded)
%              Depth                    :   25
%              Number of atoms          : 1177 (9687 expanded)
%              Number of equality atoms :  129 (1073 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t68_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 )
      <=> ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t68_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('5',plain,(
    ! [X65: $i,X67: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X65 ) @ X67 )
      | ~ ( r2_hidden @ X65 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('6',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('14',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X68 @ X69 ) )
      = ( k2_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X68 @ X69 ) )
      = ( k2_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('21',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('23',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['14','23'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('35',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['26','35','36'])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','40'])).

thf('42',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','41'])).

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

thf('43',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 )
      | ( X26 = X27 )
      | ( X26 = X28 )
      | ( X26 = X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('44',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('45',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('46',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('53',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['44','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['57'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('59',plain,(
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('60',plain,(
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

thf('61',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X35 @ X34 )
      | ~ ( zip_tseitin_0 @ X35 @ X31 @ X32 @ X33 )
      | ( X34
       != ( k1_enumset1 @ X33 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('62',plain,(
    ! [X31: $i,X32: $i,X33: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X31 @ X32 @ X33 )
      | ~ ( r2_hidden @ X35 @ ( k1_enumset1 @ X33 @ X32 @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( sk_D @ ( k1_tarski @ X0 ) @ k1_xboole_0 @ X1 ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ k1_xboole_0 @ X1 )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ k1_xboole_0 @ X1 )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ k1_xboole_0 @ X1 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ k1_xboole_0 @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('71',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('72',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('73',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('76',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74','77'])).

thf('79',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('80',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','80'])).

thf('82',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('83',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','40','82'])).

thf('84',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['81','83'])).

thf('85',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_A ) @ X0 @ ( k1_tarski @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','86'])).

thf('88',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['67','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('90',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','41'])).

thf('93',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['91','92'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('94',plain,(
    ! [X70: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X70 ) )
      = X70 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('95',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ sk_B ) ),
    inference(demod,[status(thm)],['42','95'])).

thf('97',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['91','92'])).

thf('98',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['93','94'])).

thf('99',plain,
    ( ( k1_tarski @ ( k3_tarski @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('101',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('102',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 )
      | ( r2_hidden @ X30 @ X34 )
      | ( X34
       != ( k1_enumset1 @ X33 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('103',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X30 @ ( k1_enumset1 @ X33 @ X32 @ X31 ) )
      | ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['101','103'])).

thf('105',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X26 != X25 )
      | ~ ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('106',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ~ ( zip_tseitin_0 @ X25 @ X27 @ X28 @ X25 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['104','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','107'])).

thf('109',plain,(
    r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['99','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('111',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    $false ),
    inference(demod,[status(thm)],['96','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wrBNhls7K9
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:18:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.91/1.15  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.15  % Solved by: fo/fo7.sh
% 0.91/1.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.15  % done 1184 iterations in 0.682s
% 0.91/1.15  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.15  % SZS output start Refutation
% 0.91/1.15  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.91/1.15  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.91/1.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.15  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.15  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.15  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.15  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.91/1.15  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.91/1.15  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.91/1.15  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.15  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.15  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.15  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.91/1.15  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.91/1.15  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.91/1.15  thf(t68_zfmisc_1, conjecture,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.91/1.15       ( r2_hidden @ A @ B ) ))).
% 0.91/1.15  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.15    (~( ![A:$i,B:$i]:
% 0.91/1.15        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.91/1.15          ( r2_hidden @ A @ B ) ) )),
% 0.91/1.15    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 0.91/1.15  thf('0', plain,
% 0.91/1.15      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.91/1.15        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('1', plain,
% 0.91/1.15      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.15      inference('split', [status(esa)], ['0'])).
% 0.91/1.15  thf('2', plain,
% 0.91/1.15      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.91/1.15       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.91/1.15      inference('split', [status(esa)], ['0'])).
% 0.91/1.15  thf('3', plain,
% 0.91/1.15      (((r2_hidden @ sk_A @ sk_B)
% 0.91/1.15        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('4', plain,
% 0.91/1.15      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.15      inference('split', [status(esa)], ['3'])).
% 0.91/1.15  thf(l1_zfmisc_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.91/1.15  thf('5', plain,
% 0.91/1.15      (![X65 : $i, X67 : $i]:
% 0.91/1.15         ((r1_tarski @ (k1_tarski @ X65) @ X67) | ~ (r2_hidden @ X65 @ X67))),
% 0.91/1.15      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.91/1.15  thf('6', plain,
% 0.91/1.15      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 0.91/1.15         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['4', '5'])).
% 0.91/1.15  thf(t12_xboole_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.91/1.15  thf('7', plain,
% 0.91/1.15      (![X11 : $i, X12 : $i]:
% 0.91/1.15         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.91/1.15      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.91/1.15  thf('8', plain,
% 0.91/1.15      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B)))
% 0.91/1.15         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['6', '7'])).
% 0.91/1.15  thf(t95_xboole_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( k3_xboole_0 @ A @ B ) =
% 0.91/1.15       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.91/1.15  thf('9', plain,
% 0.91/1.15      (![X21 : $i, X22 : $i]:
% 0.91/1.15         ((k3_xboole_0 @ X21 @ X22)
% 0.91/1.15           = (k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ 
% 0.91/1.15              (k2_xboole_0 @ X21 @ X22)))),
% 0.91/1.15      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.91/1.15  thf(commutativity_k5_xboole_0, axiom,
% 0.91/1.15    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.91/1.15  thf('10', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.15  thf('11', plain,
% 0.91/1.15      (![X21 : $i, X22 : $i]:
% 0.91/1.15         ((k3_xboole_0 @ X21 @ X22)
% 0.91/1.15           = (k5_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ 
% 0.91/1.15              (k5_xboole_0 @ X21 @ X22)))),
% 0.91/1.15      inference('demod', [status(thm)], ['9', '10'])).
% 0.91/1.15  thf('12', plain,
% 0.91/1.15      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.91/1.15          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))
% 0.91/1.15         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['8', '11'])).
% 0.91/1.15  thf('13', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.15  thf('14', plain,
% 0.91/1.15      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.91/1.15          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.91/1.15         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.15      inference('demod', [status(thm)], ['12', '13'])).
% 0.91/1.15  thf(commutativity_k2_tarski, axiom,
% 0.91/1.15    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.91/1.15  thf('15', plain,
% 0.91/1.15      (![X23 : $i, X24 : $i]:
% 0.91/1.15         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 0.91/1.15      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.91/1.15  thf(l51_zfmisc_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.91/1.15  thf('16', plain,
% 0.91/1.15      (![X68 : $i, X69 : $i]:
% 0.91/1.15         ((k3_tarski @ (k2_tarski @ X68 @ X69)) = (k2_xboole_0 @ X68 @ X69))),
% 0.91/1.15      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.91/1.15  thf('17', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('sup+', [status(thm)], ['15', '16'])).
% 0.91/1.15  thf('18', plain,
% 0.91/1.15      (![X68 : $i, X69 : $i]:
% 0.91/1.15         ((k3_tarski @ (k2_tarski @ X68 @ X69)) = (k2_xboole_0 @ X68 @ X69))),
% 0.91/1.15      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.91/1.15  thf('19', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('sup+', [status(thm)], ['17', '18'])).
% 0.91/1.15  thf('20', plain,
% 0.91/1.15      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B)))
% 0.91/1.15         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['6', '7'])).
% 0.91/1.15  thf('21', plain,
% 0.91/1.15      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B)))
% 0.91/1.15         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['19', '20'])).
% 0.91/1.15  thf('22', plain,
% 0.91/1.15      (![X21 : $i, X22 : $i]:
% 0.91/1.15         ((k3_xboole_0 @ X21 @ X22)
% 0.91/1.15           = (k5_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ 
% 0.91/1.15              (k5_xboole_0 @ X21 @ X22)))),
% 0.91/1.15      inference('demod', [status(thm)], ['9', '10'])).
% 0.91/1.15  thf('23', plain,
% 0.91/1.15      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.91/1.15          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.91/1.15         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['21', '22'])).
% 0.91/1.15  thf('24', plain,
% 0.91/1.15      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.91/1.15          = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.91/1.15         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['14', '23'])).
% 0.91/1.15  thf(t100_xboole_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.91/1.15  thf('25', plain,
% 0.91/1.15      (![X9 : $i, X10 : $i]:
% 0.91/1.15         ((k4_xboole_0 @ X9 @ X10)
% 0.91/1.15           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.91/1.15      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.15  thf('26', plain,
% 0.91/1.15      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.91/1.15          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.91/1.15             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.91/1.15         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['24', '25'])).
% 0.91/1.15  thf(t92_xboole_1, axiom,
% 0.91/1.15    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.91/1.15  thf('27', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.91/1.15      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.91/1.15  thf(t91_xboole_1, axiom,
% 0.91/1.15    (![A:$i,B:$i,C:$i]:
% 0.91/1.15     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.91/1.15       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.91/1.15  thf('28', plain,
% 0.91/1.15      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.91/1.15         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.91/1.15           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.91/1.15      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.91/1.15  thf('29', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.91/1.15           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['27', '28'])).
% 0.91/1.15  thf('30', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.15  thf(t5_boole, axiom,
% 0.91/1.15    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.91/1.15  thf('31', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.91/1.15      inference('cnf', [status(esa)], [t5_boole])).
% 0.91/1.15  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.15      inference('sup+', [status(thm)], ['30', '31'])).
% 0.91/1.15  thf('33', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.91/1.15      inference('demod', [status(thm)], ['29', '32'])).
% 0.91/1.15  thf('34', plain,
% 0.91/1.15      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.91/1.15          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.91/1.15         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['21', '22'])).
% 0.91/1.15  thf('35', plain,
% 0.91/1.15      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.91/1.15         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['33', '34'])).
% 0.91/1.15  thf('36', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.91/1.15      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.91/1.15  thf('37', plain,
% 0.91/1.15      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.91/1.15         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.15      inference('demod', [status(thm)], ['26', '35', '36'])).
% 0.91/1.15  thf('38', plain,
% 0.91/1.15      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 0.91/1.15         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.91/1.15      inference('split', [status(esa)], ['0'])).
% 0.91/1.15  thf('39', plain,
% 0.91/1.15      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.91/1.15         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 0.91/1.15             ((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['37', '38'])).
% 0.91/1.15  thf('40', plain,
% 0.91/1.15      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.91/1.15       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.91/1.15      inference('simplify', [status(thm)], ['39'])).
% 0.91/1.15  thf('41', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.91/1.15      inference('sat_resolution*', [status(thm)], ['2', '40'])).
% 0.91/1.15  thf('42', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.91/1.15      inference('simpl_trail', [status(thm)], ['1', '41'])).
% 0.91/1.15  thf(d1_enumset1, axiom,
% 0.91/1.15    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.15     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.91/1.15       ( ![E:$i]:
% 0.91/1.15         ( ( r2_hidden @ E @ D ) <=>
% 0.91/1.15           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.91/1.15  thf(zf_stmt_1, axiom,
% 0.91/1.15    (![E:$i,C:$i,B:$i,A:$i]:
% 0.91/1.15     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.91/1.15       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.91/1.15  thf('43', plain,
% 0.91/1.15      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.91/1.15         ((zip_tseitin_0 @ X26 @ X27 @ X28 @ X29)
% 0.91/1.15          | ((X26) = (X27))
% 0.91/1.15          | ((X26) = (X28))
% 0.91/1.15          | ((X26) = (X29)))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.15  thf(d4_xboole_0, axiom,
% 0.91/1.15    (![A:$i,B:$i,C:$i]:
% 0.91/1.15     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.91/1.15       ( ![D:$i]:
% 0.91/1.15         ( ( r2_hidden @ D @ C ) <=>
% 0.91/1.15           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.91/1.15  thf('44', plain,
% 0.91/1.15      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.91/1.15         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.91/1.15          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.91/1.15          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.91/1.15      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.91/1.15  thf(t1_boole, axiom,
% 0.91/1.15    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.91/1.15  thf('45', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.91/1.15      inference('cnf', [status(esa)], [t1_boole])).
% 0.91/1.15  thf('46', plain,
% 0.91/1.15      (![X21 : $i, X22 : $i]:
% 0.91/1.15         ((k3_xboole_0 @ X21 @ X22)
% 0.91/1.15           = (k5_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ 
% 0.91/1.15              (k5_xboole_0 @ X21 @ X22)))),
% 0.91/1.15      inference('demod', [status(thm)], ['9', '10'])).
% 0.91/1.15  thf('47', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 0.91/1.15           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['45', '46'])).
% 0.91/1.15  thf('48', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.91/1.15      inference('cnf', [status(esa)], [t5_boole])).
% 0.91/1.15  thf('49', plain,
% 0.91/1.15      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.91/1.15      inference('demod', [status(thm)], ['47', '48'])).
% 0.91/1.15  thf('50', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.91/1.15      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.91/1.15  thf('51', plain,
% 0.91/1.15      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.15      inference('demod', [status(thm)], ['49', '50'])).
% 0.91/1.15  thf('52', plain,
% 0.91/1.15      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.91/1.15         (~ (r2_hidden @ X6 @ X5)
% 0.91/1.15          | (r2_hidden @ X6 @ X3)
% 0.91/1.15          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.91/1.15      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.91/1.15  thf('53', plain,
% 0.91/1.15      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.91/1.15         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.91/1.15      inference('simplify', [status(thm)], ['52'])).
% 0.91/1.15  thf('54', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['51', '53'])).
% 0.91/1.15  thf('55', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.15         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.91/1.15          | ((X1) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 0.91/1.15          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X2))),
% 0.91/1.15      inference('sup-', [status(thm)], ['44', '54'])).
% 0.91/1.15  thf('56', plain,
% 0.91/1.15      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.15      inference('demod', [status(thm)], ['49', '50'])).
% 0.91/1.15  thf('57', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.15         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.91/1.15          | ((X1) = (k1_xboole_0))
% 0.91/1.15          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X2))),
% 0.91/1.15      inference('demod', [status(thm)], ['55', '56'])).
% 0.91/1.15  thf('58', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ X0)
% 0.91/1.15          | ((X0) = (k1_xboole_0)))),
% 0.91/1.15      inference('condensation', [status(thm)], ['57'])).
% 0.91/1.15  thf(t69_enumset1, axiom,
% 0.91/1.15    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.91/1.15  thf('59', plain,
% 0.91/1.15      (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 0.91/1.15      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.91/1.15  thf(t70_enumset1, axiom,
% 0.91/1.15    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.91/1.15  thf('60', plain,
% 0.91/1.15      (![X38 : $i, X39 : $i]:
% 0.91/1.15         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.91/1.15      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.91/1.15  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.91/1.15  thf(zf_stmt_3, axiom,
% 0.91/1.15    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.15     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.91/1.15       ( ![E:$i]:
% 0.91/1.15         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.91/1.15  thf('61', plain,
% 0.91/1.15      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.91/1.15         (~ (r2_hidden @ X35 @ X34)
% 0.91/1.15          | ~ (zip_tseitin_0 @ X35 @ X31 @ X32 @ X33)
% 0.91/1.15          | ((X34) != (k1_enumset1 @ X33 @ X32 @ X31)))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.15  thf('62', plain,
% 0.91/1.15      (![X31 : $i, X32 : $i, X33 : $i, X35 : $i]:
% 0.91/1.15         (~ (zip_tseitin_0 @ X35 @ X31 @ X32 @ X33)
% 0.91/1.15          | ~ (r2_hidden @ X35 @ (k1_enumset1 @ X33 @ X32 @ X31)))),
% 0.91/1.15      inference('simplify', [status(thm)], ['61'])).
% 0.91/1.15  thf('63', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.15         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.91/1.15          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.91/1.15      inference('sup-', [status(thm)], ['60', '62'])).
% 0.91/1.15  thf('64', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.91/1.15          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['59', '63'])).
% 0.91/1.15  thf('65', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.91/1.15          | ~ (zip_tseitin_0 @ (sk_D @ (k1_tarski @ X0) @ k1_xboole_0 @ X1) @ 
% 0.91/1.15               X0 @ X0 @ X0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['58', '64'])).
% 0.91/1.15  thf('66', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (((sk_D @ (k1_tarski @ X0) @ k1_xboole_0 @ X1) = (X0))
% 0.91/1.15          | ((sk_D @ (k1_tarski @ X0) @ k1_xboole_0 @ X1) = (X0))
% 0.91/1.15          | ((sk_D @ (k1_tarski @ X0) @ k1_xboole_0 @ X1) = (X0))
% 0.91/1.15          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['43', '65'])).
% 0.91/1.15  thf('67', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.91/1.15          | ((sk_D @ (k1_tarski @ X0) @ k1_xboole_0 @ X1) = (X0)))),
% 0.91/1.15      inference('simplify', [status(thm)], ['66'])).
% 0.91/1.15  thf('68', plain,
% 0.91/1.15      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.91/1.15         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.91/1.15          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.91/1.15          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.91/1.15      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.91/1.15  thf('69', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.91/1.15          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.91/1.15      inference('eq_fact', [status(thm)], ['68'])).
% 0.91/1.15  thf('70', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.91/1.15      inference('demod', [status(thm)], ['29', '32'])).
% 0.91/1.15  thf('71', plain,
% 0.91/1.15      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.91/1.15         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.91/1.15      inference('split', [status(esa)], ['3'])).
% 0.91/1.15  thf(t39_xboole_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.91/1.15  thf('72', plain,
% 0.91/1.15      (![X14 : $i, X15 : $i]:
% 0.91/1.15         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.91/1.15           = (k2_xboole_0 @ X14 @ X15))),
% 0.91/1.15      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.91/1.15  thf('73', plain,
% 0.91/1.15      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.91/1.15          = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.91/1.15         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.91/1.15      inference('sup+', [status(thm)], ['71', '72'])).
% 0.91/1.15  thf('74', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('sup+', [status(thm)], ['17', '18'])).
% 0.91/1.15  thf('75', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.15      inference('sup+', [status(thm)], ['17', '18'])).
% 0.91/1.15  thf('76', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.91/1.15      inference('cnf', [status(esa)], [t1_boole])).
% 0.91/1.15  thf('77', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.15      inference('sup+', [status(thm)], ['75', '76'])).
% 0.91/1.15  thf('78', plain,
% 0.91/1.15      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.91/1.15         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.91/1.15      inference('demod', [status(thm)], ['73', '74', '77'])).
% 0.91/1.15  thf('79', plain,
% 0.91/1.15      (![X21 : $i, X22 : $i]:
% 0.91/1.15         ((k3_xboole_0 @ X21 @ X22)
% 0.91/1.15           = (k5_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ 
% 0.91/1.15              (k5_xboole_0 @ X21 @ X22)))),
% 0.91/1.15      inference('demod', [status(thm)], ['9', '10'])).
% 0.91/1.15  thf('80', plain,
% 0.91/1.15      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.91/1.15          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.91/1.15         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.91/1.15      inference('sup+', [status(thm)], ['78', '79'])).
% 0.91/1.15  thf('81', plain,
% 0.91/1.15      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.91/1.15         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.91/1.15      inference('sup+', [status(thm)], ['70', '80'])).
% 0.91/1.15  thf('82', plain,
% 0.91/1.15      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.91/1.15       ((r2_hidden @ sk_A @ sk_B))),
% 0.91/1.15      inference('split', [status(esa)], ['3'])).
% 0.91/1.15  thf('83', plain,
% 0.91/1.15      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.91/1.15      inference('sat_resolution*', [status(thm)], ['2', '40', '82'])).
% 0.91/1.15  thf('84', plain,
% 0.91/1.15      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.91/1.15      inference('simpl_trail', [status(thm)], ['81', '83'])).
% 0.91/1.15  thf('85', plain,
% 0.91/1.15      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.91/1.15         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.91/1.15      inference('simplify', [status(thm)], ['52'])).
% 0.91/1.15  thf('86', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)) | (r2_hidden @ X0 @ sk_B))),
% 0.91/1.15      inference('sup-', [status(thm)], ['84', '85'])).
% 0.91/1.15  thf('87', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         (((k1_tarski @ sk_A) = (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.91/1.15          | (r2_hidden @ 
% 0.91/1.15             (sk_D @ (k1_tarski @ sk_A) @ X0 @ (k1_tarski @ sk_A)) @ sk_B))),
% 0.91/1.15      inference('sup-', [status(thm)], ['69', '86'])).
% 0.91/1.15  thf('88', plain,
% 0.91/1.15      (((r2_hidden @ sk_A @ sk_B)
% 0.91/1.15        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.91/1.15        | ((k1_tarski @ sk_A)
% 0.91/1.15            = (k3_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['67', '87'])).
% 0.91/1.15  thf('89', plain,
% 0.91/1.15      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.15      inference('demod', [status(thm)], ['49', '50'])).
% 0.91/1.15  thf('90', plain,
% 0.91/1.15      (((r2_hidden @ sk_A @ sk_B)
% 0.91/1.15        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.91/1.15        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.91/1.15      inference('demod', [status(thm)], ['88', '89'])).
% 0.91/1.15  thf('91', plain,
% 0.91/1.15      ((((k1_tarski @ sk_A) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B))),
% 0.91/1.15      inference('simplify', [status(thm)], ['90'])).
% 0.91/1.15  thf('92', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.91/1.15      inference('simpl_trail', [status(thm)], ['1', '41'])).
% 0.91/1.15  thf('93', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.91/1.15      inference('clc', [status(thm)], ['91', '92'])).
% 0.91/1.15  thf(t31_zfmisc_1, axiom,
% 0.91/1.15    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.91/1.15  thf('94', plain, (![X70 : $i]: ((k3_tarski @ (k1_tarski @ X70)) = (X70))),
% 0.91/1.15      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.91/1.15  thf('95', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.91/1.15      inference('sup+', [status(thm)], ['93', '94'])).
% 0.91/1.15  thf('96', plain, (~ (r2_hidden @ (k3_tarski @ k1_xboole_0) @ sk_B)),
% 0.91/1.15      inference('demod', [status(thm)], ['42', '95'])).
% 0.91/1.15  thf('97', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.91/1.15      inference('clc', [status(thm)], ['91', '92'])).
% 0.91/1.15  thf('98', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.91/1.15      inference('sup+', [status(thm)], ['93', '94'])).
% 0.91/1.15  thf('99', plain, (((k1_tarski @ (k3_tarski @ k1_xboole_0)) = (k1_xboole_0))),
% 0.91/1.15      inference('demod', [status(thm)], ['97', '98'])).
% 0.91/1.15  thf('100', plain,
% 0.91/1.15      (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 0.91/1.15      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.91/1.15  thf('101', plain,
% 0.91/1.15      (![X38 : $i, X39 : $i]:
% 0.91/1.15         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.91/1.15      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.91/1.15  thf('102', plain,
% 0.91/1.15      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.91/1.15         ((zip_tseitin_0 @ X30 @ X31 @ X32 @ X33)
% 0.91/1.15          | (r2_hidden @ X30 @ X34)
% 0.91/1.15          | ((X34) != (k1_enumset1 @ X33 @ X32 @ X31)))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.15  thf('103', plain,
% 0.91/1.15      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.91/1.15         ((r2_hidden @ X30 @ (k1_enumset1 @ X33 @ X32 @ X31))
% 0.91/1.15          | (zip_tseitin_0 @ X30 @ X31 @ X32 @ X33))),
% 0.91/1.15      inference('simplify', [status(thm)], ['102'])).
% 0.91/1.15  thf('104', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.15         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.91/1.15          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.91/1.15      inference('sup+', [status(thm)], ['101', '103'])).
% 0.91/1.15  thf('105', plain,
% 0.91/1.15      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.91/1.15         (((X26) != (X25)) | ~ (zip_tseitin_0 @ X26 @ X27 @ X28 @ X25))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.15  thf('106', plain,
% 0.91/1.15      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.91/1.15         ~ (zip_tseitin_0 @ X25 @ X27 @ X28 @ X25)),
% 0.91/1.15      inference('simplify', [status(thm)], ['105'])).
% 0.91/1.15  thf('107', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.91/1.15      inference('sup-', [status(thm)], ['104', '106'])).
% 0.91/1.15  thf('108', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.91/1.15      inference('sup+', [status(thm)], ['100', '107'])).
% 0.91/1.15  thf('109', plain, ((r2_hidden @ (k3_tarski @ k1_xboole_0) @ k1_xboole_0)),
% 0.91/1.15      inference('sup+', [status(thm)], ['99', '108'])).
% 0.91/1.15  thf('110', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['51', '53'])).
% 0.91/1.15  thf('111', plain, (![X0 : $i]: (r2_hidden @ (k3_tarski @ k1_xboole_0) @ X0)),
% 0.91/1.15      inference('sup-', [status(thm)], ['109', '110'])).
% 0.91/1.15  thf('112', plain, ($false), inference('demod', [status(thm)], ['96', '111'])).
% 0.91/1.15  
% 0.91/1.15  % SZS output end Refutation
% 0.91/1.15  
% 0.91/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
