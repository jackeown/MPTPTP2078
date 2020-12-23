%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bc7K6U2YCt

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:13 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 522 expanded)
%              Number of leaves         :   26 ( 181 expanded)
%              Depth                    :   20
%              Number of atoms          :  743 (4233 expanded)
%              Number of equality atoms :   83 ( 510 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('12',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('16',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','20'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','19'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','25'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X73: $i,X74: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X73 @ X74 ) )
      = ( k2_xboole_0 @ X73 @ X74 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X73: $i,X74: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X73 @ X74 ) )
      = ( k2_xboole_0 @ X73 @ X74 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('34',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','19'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('39',plain,(
    ! [X75: $i,X76: $i,X77: $i] :
      ( ( X75 != X77 )
      | ~ ( r2_hidden @ X75 @ ( k4_xboole_0 @ X76 @ ( k1_tarski @ X77 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('40',plain,(
    ! [X76: $i,X77: $i] :
      ~ ( r2_hidden @ X77 @ ( k4_xboole_0 @ X76 @ ( k1_tarski @ X77 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','41'])).

thf('43',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','42'])).

thf('44',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','43'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('45',plain,(
    ! [X71: $i,X72: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X71 ) @ X72 )
      | ( r2_hidden @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('46',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ X1 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('54',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k2_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('55',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','54','55','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('65',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('66',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','42','65'])).

thf('67',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['64','66'])).

thf('68',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','67'])).

thf('69',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['44','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bc7K6U2YCt
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:54:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.59/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.83  % Solved by: fo/fo7.sh
% 0.59/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.83  % done 741 iterations in 0.370s
% 0.59/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.83  % SZS output start Refutation
% 0.59/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.83  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.83  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.59/0.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.83  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.83  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.83  thf(t67_zfmisc_1, conjecture,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.59/0.83       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.59/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.83    (~( ![A:$i,B:$i]:
% 0.59/0.83        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.59/0.83          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.59/0.83    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.59/0.83  thf('0', plain,
% 0.59/0.83      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.59/0.83        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('1', plain,
% 0.59/0.83      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.59/0.83      inference('split', [status(esa)], ['0'])).
% 0.59/0.83  thf('2', plain,
% 0.59/0.83      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.59/0.83       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.59/0.83      inference('split', [status(esa)], ['0'])).
% 0.59/0.83  thf('3', plain,
% 0.59/0.83      (((r2_hidden @ sk_A @ sk_B)
% 0.59/0.83        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('4', plain,
% 0.59/0.83      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.59/0.83      inference('split', [status(esa)], ['3'])).
% 0.59/0.83  thf('5', plain,
% 0.59/0.83      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.59/0.83         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.59/0.83      inference('split', [status(esa)], ['0'])).
% 0.59/0.83  thf(t95_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( k3_xboole_0 @ A @ B ) =
% 0.59/0.83       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.59/0.83  thf('6', plain,
% 0.59/0.83      (![X20 : $i, X21 : $i]:
% 0.59/0.83         ((k3_xboole_0 @ X20 @ X21)
% 0.59/0.83           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.59/0.83              (k2_xboole_0 @ X20 @ X21)))),
% 0.59/0.83      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.59/0.83  thf(t91_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i]:
% 0.59/0.83     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.83       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.59/0.83  thf('7', plain,
% 0.59/0.83      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.83         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.59/0.83           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.59/0.83      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.59/0.83  thf('8', plain,
% 0.59/0.83      (![X20 : $i, X21 : $i]:
% 0.59/0.83         ((k3_xboole_0 @ X20 @ X21)
% 0.59/0.83           = (k5_xboole_0 @ X20 @ 
% 0.59/0.83              (k5_xboole_0 @ X21 @ (k2_xboole_0 @ X20 @ X21))))),
% 0.59/0.83      inference('demod', [status(thm)], ['6', '7'])).
% 0.59/0.83  thf(t92_xboole_1, axiom,
% 0.59/0.83    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.59/0.83  thf('9', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.59/0.83      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.59/0.83  thf('10', plain,
% 0.59/0.83      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.83         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.59/0.83           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.59/0.83      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.59/0.83  thf('11', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.59/0.83           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['9', '10'])).
% 0.59/0.83  thf(idempotence_k2_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.59/0.83  thf('12', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.59/0.83      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.59/0.83  thf('13', plain,
% 0.59/0.83      (![X20 : $i, X21 : $i]:
% 0.59/0.83         ((k3_xboole_0 @ X20 @ X21)
% 0.59/0.83           = (k5_xboole_0 @ X20 @ 
% 0.59/0.83              (k5_xboole_0 @ X21 @ (k2_xboole_0 @ X20 @ X21))))),
% 0.59/0.83      inference('demod', [status(thm)], ['6', '7'])).
% 0.59/0.83  thf('14', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((k3_xboole_0 @ X0 @ X0)
% 0.59/0.83           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.83  thf(idempotence_k3_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.59/0.83  thf('15', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.59/0.83      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.59/0.83  thf('16', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.59/0.83      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.59/0.83  thf('17', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.83      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.59/0.83  thf(commutativity_k5_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.59/0.83  thf('18', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.59/0.83  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.59/0.83      inference('sup+', [status(thm)], ['17', '18'])).
% 0.59/0.83  thf('20', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.59/0.83      inference('demod', [status(thm)], ['11', '19'])).
% 0.59/0.83  thf('21', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.59/0.83           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['8', '20'])).
% 0.59/0.83  thf(t100_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.83  thf('22', plain,
% 0.59/0.83      (![X4 : $i, X5 : $i]:
% 0.59/0.83         ((k4_xboole_0 @ X4 @ X5)
% 0.59/0.83           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.59/0.83      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.83  thf('23', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.59/0.83           = (k4_xboole_0 @ X1 @ X0))),
% 0.59/0.83      inference('demod', [status(thm)], ['21', '22'])).
% 0.59/0.83  thf('24', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.59/0.83      inference('demod', [status(thm)], ['11', '19'])).
% 0.59/0.83  thf('25', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k2_xboole_0 @ X1 @ X0)
% 0.59/0.83           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['23', '24'])).
% 0.59/0.83  thf('26', plain,
% 0.59/0.83      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.59/0.83          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.59/0.83         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.59/0.83      inference('sup+', [status(thm)], ['5', '25'])).
% 0.59/0.83  thf(commutativity_k2_tarski, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.59/0.83  thf('27', plain,
% 0.59/0.83      (![X22 : $i, X23 : $i]:
% 0.59/0.83         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 0.59/0.83      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.59/0.83  thf(l51_zfmisc_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.83  thf('28', plain,
% 0.59/0.83      (![X73 : $i, X74 : $i]:
% 0.59/0.83         ((k3_tarski @ (k2_tarski @ X73 @ X74)) = (k2_xboole_0 @ X73 @ X74))),
% 0.59/0.83      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.59/0.83  thf('29', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['27', '28'])).
% 0.59/0.83  thf('30', plain,
% 0.59/0.83      (![X73 : $i, X74 : $i]:
% 0.59/0.83         ((k3_tarski @ (k2_tarski @ X73 @ X74)) = (k2_xboole_0 @ X73 @ X74))),
% 0.59/0.83      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.59/0.83  thf('31', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['29', '30'])).
% 0.59/0.83  thf('32', plain,
% 0.59/0.83      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.59/0.83          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.59/0.83         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.59/0.83      inference('demod', [status(thm)], ['26', '31'])).
% 0.59/0.83  thf('33', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.59/0.83           = (k4_xboole_0 @ X1 @ X0))),
% 0.59/0.83      inference('demod', [status(thm)], ['21', '22'])).
% 0.59/0.83  thf('34', plain,
% 0.59/0.83      ((((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.59/0.83          (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.59/0.83          = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.59/0.83         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.59/0.83      inference('sup+', [status(thm)], ['32', '33'])).
% 0.59/0.83  thf('35', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.59/0.83  thf('36', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.59/0.83      inference('demod', [status(thm)], ['11', '19'])).
% 0.59/0.83  thf('37', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['35', '36'])).
% 0.59/0.83  thf('38', plain,
% 0.59/0.83      ((((sk_B) = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.59/0.83         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.59/0.83      inference('demod', [status(thm)], ['34', '37'])).
% 0.59/0.83  thf(t64_zfmisc_1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i]:
% 0.59/0.83     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.59/0.83       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.59/0.83  thf('39', plain,
% 0.59/0.83      (![X75 : $i, X76 : $i, X77 : $i]:
% 0.59/0.83         (((X75) != (X77))
% 0.59/0.83          | ~ (r2_hidden @ X75 @ (k4_xboole_0 @ X76 @ (k1_tarski @ X77))))),
% 0.59/0.83      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.59/0.83  thf('40', plain,
% 0.59/0.83      (![X76 : $i, X77 : $i]:
% 0.59/0.83         ~ (r2_hidden @ X77 @ (k4_xboole_0 @ X76 @ (k1_tarski @ X77)))),
% 0.59/0.83      inference('simplify', [status(thm)], ['39'])).
% 0.59/0.83  thf('41', plain,
% 0.59/0.83      ((~ (r2_hidden @ sk_A @ sk_B))
% 0.59/0.83         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.59/0.83      inference('sup-', [status(thm)], ['38', '40'])).
% 0.59/0.83  thf('42', plain,
% 0.59/0.83      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.59/0.83       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.59/0.83      inference('sup-', [status(thm)], ['4', '41'])).
% 0.59/0.83  thf('43', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.59/0.83      inference('sat_resolution*', [status(thm)], ['2', '42'])).
% 0.59/0.83  thf('44', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.59/0.83      inference('simpl_trail', [status(thm)], ['1', '43'])).
% 0.59/0.83  thf(l27_zfmisc_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.59/0.83  thf('45', plain,
% 0.59/0.83      (![X71 : $i, X72 : $i]:
% 0.59/0.83         ((r1_xboole_0 @ (k1_tarski @ X71) @ X72) | (r2_hidden @ X71 @ X72))),
% 0.59/0.83      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.59/0.83  thf(t88_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( r1_xboole_0 @ A @ B ) =>
% 0.59/0.83       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.59/0.83  thf('46', plain,
% 0.59/0.83      (![X14 : $i, X15 : $i]:
% 0.59/0.83         (((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15) = (X14))
% 0.59/0.83          | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.59/0.83      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.59/0.83  thf('47', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((r2_hidden @ X1 @ X0)
% 0.59/0.83          | ((k4_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0) @ X0)
% 0.59/0.83              = (k1_tarski @ X1)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['45', '46'])).
% 0.59/0.83  thf('48', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.59/0.83           = (k4_xboole_0 @ X1 @ X0))),
% 0.59/0.83      inference('demod', [status(thm)], ['21', '22'])).
% 0.59/0.83  thf('49', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['35', '36'])).
% 0.59/0.83  thf('50', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((X0)
% 0.59/0.83           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['48', '49'])).
% 0.59/0.83  thf('51', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.59/0.83  thf('52', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((X0)
% 0.59/0.83           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.83      inference('demod', [status(thm)], ['50', '51'])).
% 0.59/0.83  thf('53', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (((X1)
% 0.59/0.83            = (k5_xboole_0 @ (k1_tarski @ X0) @ 
% 0.59/0.83               (k2_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1) @ X1)))
% 0.59/0.83          | (r2_hidden @ X0 @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['47', '52'])).
% 0.59/0.83  thf(t4_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i]:
% 0.59/0.83     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.83       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.59/0.83  thf('54', plain,
% 0.59/0.83      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.59/0.83         ((k2_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X11)
% 0.59/0.83           = (k2_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.59/0.83      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.59/0.83  thf('55', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.59/0.83      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.59/0.83  thf('56', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['29', '30'])).
% 0.59/0.83  thf('57', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.59/0.83           = (k4_xboole_0 @ X1 @ X0))),
% 0.59/0.83      inference('demod', [status(thm)], ['21', '22'])).
% 0.59/0.83  thf('58', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.59/0.83           = (k4_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['56', '57'])).
% 0.59/0.83  thf('59', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.59/0.83          | (r2_hidden @ X0 @ X1))),
% 0.59/0.83      inference('demod', [status(thm)], ['53', '54', '55', '58'])).
% 0.59/0.83  thf('60', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((X0)
% 0.59/0.83           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.83      inference('demod', [status(thm)], ['50', '51'])).
% 0.59/0.83  thf('61', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (((k1_tarski @ X1)
% 0.59/0.83            = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ (k1_tarski @ X1))))
% 0.59/0.83          | (r2_hidden @ X1 @ X0))),
% 0.59/0.83      inference('sup+', [status(thm)], ['59', '60'])).
% 0.59/0.83  thf('62', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.59/0.83           = (k4_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['56', '57'])).
% 0.59/0.83  thf('63', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (((k1_tarski @ X1) = (k4_xboole_0 @ (k1_tarski @ X1) @ X0))
% 0.59/0.83          | (r2_hidden @ X1 @ X0))),
% 0.59/0.83      inference('demod', [status(thm)], ['61', '62'])).
% 0.59/0.83  thf('64', plain,
% 0.59/0.83      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))
% 0.59/0.83         <= (~
% 0.59/0.83             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.59/0.83      inference('split', [status(esa)], ['3'])).
% 0.59/0.83  thf('65', plain,
% 0.59/0.83      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.59/0.83       ((r2_hidden @ sk_A @ sk_B))),
% 0.59/0.83      inference('split', [status(esa)], ['3'])).
% 0.59/0.83  thf('66', plain,
% 0.59/0.83      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.59/0.83      inference('sat_resolution*', [status(thm)], ['2', '42', '65'])).
% 0.59/0.83  thf('67', plain,
% 0.59/0.83      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.59/0.83      inference('simpl_trail', [status(thm)], ['64', '66'])).
% 0.59/0.83  thf('68', plain,
% 0.59/0.83      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.59/0.83      inference('sup-', [status(thm)], ['63', '67'])).
% 0.59/0.83  thf('69', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.59/0.83      inference('simplify', [status(thm)], ['68'])).
% 0.59/0.83  thf('70', plain, ($false), inference('demod', [status(thm)], ['44', '69'])).
% 0.59/0.83  
% 0.59/0.83  % SZS output end Refutation
% 0.59/0.83  
% 0.59/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
