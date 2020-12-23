%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A2lUwxLXg1

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:22 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 248 expanded)
%              Number of leaves         :   34 (  89 expanded)
%              Depth                    :   19
%              Number of atoms          :  780 (1869 expanded)
%              Number of equality atoms :   86 ( 219 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('4',plain,(
    ! [X67: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X67 ) )
      = X67 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X65 @ X66 ) )
      = ( k2_xboole_0 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('11',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('13',plain,(
    ! [X62: $i,X64: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X62 ) @ X64 )
      | ~ ( r2_hidden @ X62 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('14',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ X0 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ X0 @ sk_B ) )
        = ( k2_xboole_0 @ X0 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ X0 @ sk_B ) )
        = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ X0 @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['20','23','26','27','30'])).

thf('32',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['7','31'])).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36'])).

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

thf('43',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('44',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('45',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','40','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('48',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('49',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','57'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('62',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('64',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
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

thf('65',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 )
      | ( r2_hidden @ X27 @ X31 )
      | ( X31
       != ( k1_enumset1 @ X30 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('66',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X27 @ ( k1_enumset1 @ X30 @ X29 @ X28 ) )
      | ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X23 != X22 )
      | ~ ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('69',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ~ ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X22 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','70'])).

thf('72',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['62','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['42','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A2lUwxLXg1
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.11  % Solved by: fo/fo7.sh
% 0.91/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.11  % done 1140 iterations in 0.647s
% 0.91/1.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.11  % SZS output start Refutation
% 0.91/1.11  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.91/1.11  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.91/1.11  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.11  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.91/1.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.11  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.11  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.91/1.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.11  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.91/1.11  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.91/1.11  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.91/1.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.11  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.11  thf(t68_zfmisc_1, conjecture,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.91/1.11       ( r2_hidden @ A @ B ) ))).
% 0.91/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.11    (~( ![A:$i,B:$i]:
% 0.91/1.11        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.91/1.11          ( r2_hidden @ A @ B ) ) )),
% 0.91/1.11    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 0.91/1.11  thf('0', plain,
% 0.91/1.11      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.91/1.11        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('1', plain,
% 0.91/1.11      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.11      inference('split', [status(esa)], ['0'])).
% 0.91/1.11  thf('2', plain,
% 0.91/1.11      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.91/1.11       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.91/1.11      inference('split', [status(esa)], ['0'])).
% 0.91/1.11  thf(t69_enumset1, axiom,
% 0.91/1.11    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.91/1.11  thf('3', plain, (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.91/1.11      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.91/1.11  thf(t31_zfmisc_1, axiom,
% 0.91/1.11    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.91/1.11  thf('4', plain, (![X67 : $i]: ((k3_tarski @ (k1_tarski @ X67)) = (X67))),
% 0.91/1.11      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.91/1.11  thf('5', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.91/1.11      inference('sup+', [status(thm)], ['3', '4'])).
% 0.91/1.11  thf(l51_zfmisc_1, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.91/1.11  thf('6', plain,
% 0.91/1.11      (![X65 : $i, X66 : $i]:
% 0.91/1.11         ((k3_tarski @ (k2_tarski @ X65 @ X66)) = (k2_xboole_0 @ X65 @ X66))),
% 0.91/1.11      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.91/1.11  thf('7', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.91/1.11      inference('demod', [status(thm)], ['5', '6'])).
% 0.91/1.11  thf('8', plain,
% 0.91/1.11      (((r2_hidden @ sk_A @ sk_B)
% 0.91/1.11        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('9', plain,
% 0.91/1.11      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.11      inference('split', [status(esa)], ['8'])).
% 0.91/1.11  thf(d3_xboole_0, axiom,
% 0.91/1.11    (![A:$i,B:$i,C:$i]:
% 0.91/1.11     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.91/1.11       ( ![D:$i]:
% 0.91/1.11         ( ( r2_hidden @ D @ C ) <=>
% 0.91/1.11           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.91/1.11  thf('10', plain,
% 0.91/1.11      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.11         (~ (r2_hidden @ X4 @ X5)
% 0.91/1.11          | (r2_hidden @ X4 @ X6)
% 0.91/1.11          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.91/1.11      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.91/1.11  thf('11', plain,
% 0.91/1.11      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.91/1.11         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.91/1.11      inference('simplify', [status(thm)], ['10'])).
% 0.91/1.11  thf('12', plain,
% 0.91/1.11      ((![X0 : $i]: (r2_hidden @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))
% 0.91/1.11         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['9', '11'])).
% 0.91/1.11  thf(l1_zfmisc_1, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.91/1.11  thf('13', plain,
% 0.91/1.11      (![X62 : $i, X64 : $i]:
% 0.91/1.11         ((r1_tarski @ (k1_tarski @ X62) @ X64) | ~ (r2_hidden @ X62 @ X64))),
% 0.91/1.11      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.91/1.11  thf('14', plain,
% 0.91/1.11      ((![X0 : $i]:
% 0.91/1.11          (r1_tarski @ (k1_tarski @ sk_A) @ (k2_xboole_0 @ X0 @ sk_B)))
% 0.91/1.11         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['12', '13'])).
% 0.91/1.11  thf(t12_xboole_1, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.91/1.11  thf('15', plain,
% 0.91/1.11      (![X13 : $i, X14 : $i]:
% 0.91/1.11         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 0.91/1.11      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.91/1.11  thf('16', plain,
% 0.91/1.11      ((![X0 : $i]:
% 0.91/1.11          ((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_xboole_0 @ X0 @ sk_B))
% 0.91/1.11            = (k2_xboole_0 @ X0 @ sk_B)))
% 0.91/1.11         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['14', '15'])).
% 0.91/1.11  thf(t95_xboole_1, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( k3_xboole_0 @ A @ B ) =
% 0.91/1.11       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.91/1.11  thf('17', plain,
% 0.91/1.11      (![X20 : $i, X21 : $i]:
% 0.91/1.11         ((k3_xboole_0 @ X20 @ X21)
% 0.91/1.11           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.91/1.11              (k2_xboole_0 @ X20 @ X21)))),
% 0.91/1.11      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.91/1.11  thf(t91_xboole_1, axiom,
% 0.91/1.11    (![A:$i,B:$i,C:$i]:
% 0.91/1.11     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.91/1.11       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.91/1.11  thf('18', plain,
% 0.91/1.11      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.11         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.91/1.11           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.91/1.11      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.91/1.11  thf('19', plain,
% 0.91/1.11      (![X20 : $i, X21 : $i]:
% 0.91/1.11         ((k3_xboole_0 @ X20 @ X21)
% 0.91/1.11           = (k5_xboole_0 @ X20 @ 
% 0.91/1.11              (k5_xboole_0 @ X21 @ (k2_xboole_0 @ X20 @ X21))))),
% 0.91/1.11      inference('demod', [status(thm)], ['17', '18'])).
% 0.91/1.11  thf('20', plain,
% 0.91/1.11      ((![X0 : $i]:
% 0.91/1.11          ((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_xboole_0 @ X0 @ sk_B))
% 0.91/1.11            = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.91/1.11               (k5_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ 
% 0.91/1.11                (k2_xboole_0 @ X0 @ sk_B)))))
% 0.91/1.11         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.11      inference('sup+', [status(thm)], ['16', '19'])).
% 0.91/1.11  thf(idempotence_k3_xboole_0, axiom,
% 0.91/1.11    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.91/1.11  thf('21', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 0.91/1.11      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.91/1.11  thf(t100_xboole_1, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.91/1.11  thf('22', plain,
% 0.91/1.11      (![X11 : $i, X12 : $i]:
% 0.91/1.11         ((k4_xboole_0 @ X11 @ X12)
% 0.91/1.11           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.91/1.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.11  thf('23', plain,
% 0.91/1.11      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.91/1.11      inference('sup+', [status(thm)], ['21', '22'])).
% 0.91/1.11  thf('24', plain,
% 0.91/1.11      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.91/1.11      inference('sup+', [status(thm)], ['21', '22'])).
% 0.91/1.11  thf(t92_xboole_1, axiom,
% 0.91/1.11    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.91/1.11  thf('25', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.91/1.11      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.91/1.11  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.11      inference('sup+', [status(thm)], ['24', '25'])).
% 0.91/1.11  thf(commutativity_k5_xboole_0, axiom,
% 0.91/1.11    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.91/1.11  thf('27', plain,
% 0.91/1.11      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.91/1.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.11  thf('28', plain,
% 0.91/1.11      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.91/1.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.11  thf(t5_boole, axiom,
% 0.91/1.11    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.91/1.11  thf('29', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.91/1.11      inference('cnf', [status(esa)], [t5_boole])).
% 0.91/1.11  thf('30', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.11      inference('sup+', [status(thm)], ['28', '29'])).
% 0.91/1.11  thf('31', plain,
% 0.91/1.11      ((![X0 : $i]:
% 0.91/1.11          ((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_xboole_0 @ X0 @ sk_B))
% 0.91/1.11            = (k1_tarski @ sk_A)))
% 0.91/1.11         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.11      inference('demod', [status(thm)], ['20', '23', '26', '27', '30'])).
% 0.91/1.11  thf('32', plain,
% 0.91/1.11      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.91/1.11         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.11      inference('sup+', [status(thm)], ['7', '31'])).
% 0.91/1.11  thf('33', plain,
% 0.91/1.11      (![X11 : $i, X12 : $i]:
% 0.91/1.11         ((k4_xboole_0 @ X11 @ X12)
% 0.91/1.11           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.91/1.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.11  thf('34', plain,
% 0.91/1.11      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.91/1.11          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))
% 0.91/1.11         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.11      inference('sup+', [status(thm)], ['32', '33'])).
% 0.91/1.11  thf('35', plain,
% 0.91/1.11      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.91/1.11      inference('sup+', [status(thm)], ['21', '22'])).
% 0.91/1.11  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.11      inference('sup+', [status(thm)], ['24', '25'])).
% 0.91/1.11  thf('37', plain,
% 0.91/1.11      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.91/1.11         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.11      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.91/1.11  thf('38', plain,
% 0.91/1.11      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 0.91/1.11         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.91/1.11      inference('split', [status(esa)], ['0'])).
% 0.91/1.11  thf('39', plain,
% 0.91/1.11      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.91/1.11         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 0.91/1.11             ((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['37', '38'])).
% 0.91/1.11  thf('40', plain,
% 0.91/1.11      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.91/1.11       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.91/1.11      inference('simplify', [status(thm)], ['39'])).
% 0.91/1.11  thf('41', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.91/1.11      inference('sat_resolution*', [status(thm)], ['2', '40'])).
% 0.91/1.11  thf('42', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.91/1.11      inference('simpl_trail', [status(thm)], ['1', '41'])).
% 0.91/1.11  thf('43', plain,
% 0.91/1.11      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.91/1.11         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.91/1.11      inference('split', [status(esa)], ['8'])).
% 0.91/1.11  thf('44', plain,
% 0.91/1.11      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.91/1.11       ((r2_hidden @ sk_A @ sk_B))),
% 0.91/1.11      inference('split', [status(esa)], ['8'])).
% 0.91/1.11  thf('45', plain,
% 0.91/1.11      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.91/1.11      inference('sat_resolution*', [status(thm)], ['2', '40', '44'])).
% 0.91/1.11  thf('46', plain,
% 0.91/1.11      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.91/1.11      inference('simpl_trail', [status(thm)], ['43', '45'])).
% 0.91/1.11  thf('47', plain,
% 0.91/1.11      (![X20 : $i, X21 : $i]:
% 0.91/1.11         ((k3_xboole_0 @ X20 @ X21)
% 0.91/1.11           = (k5_xboole_0 @ X20 @ 
% 0.91/1.11              (k5_xboole_0 @ X21 @ (k2_xboole_0 @ X20 @ X21))))),
% 0.91/1.11      inference('demod', [status(thm)], ['17', '18'])).
% 0.91/1.11  thf('48', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.91/1.11      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.91/1.11  thf('49', plain,
% 0.91/1.11      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.11         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.91/1.11           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.91/1.11      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.91/1.11  thf('50', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.91/1.11           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.91/1.11      inference('sup+', [status(thm)], ['48', '49'])).
% 0.91/1.11  thf('51', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.11      inference('sup+', [status(thm)], ['28', '29'])).
% 0.91/1.11  thf('52', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.91/1.11      inference('demod', [status(thm)], ['50', '51'])).
% 0.91/1.11  thf('53', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.91/1.11           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.11      inference('sup+', [status(thm)], ['47', '52'])).
% 0.91/1.11  thf('54', plain,
% 0.91/1.11      (![X11 : $i, X12 : $i]:
% 0.91/1.11         ((k4_xboole_0 @ X11 @ X12)
% 0.91/1.11           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.91/1.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.11  thf('55', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.91/1.11           = (k4_xboole_0 @ X1 @ X0))),
% 0.91/1.11      inference('demod', [status(thm)], ['53', '54'])).
% 0.91/1.11  thf('56', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.91/1.11      inference('demod', [status(thm)], ['50', '51'])).
% 0.91/1.11  thf('57', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         ((k2_xboole_0 @ X1 @ X0)
% 0.91/1.11           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.91/1.11      inference('sup+', [status(thm)], ['55', '56'])).
% 0.91/1.11  thf('58', plain,
% 0.91/1.11      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.91/1.11         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.91/1.11      inference('sup+', [status(thm)], ['46', '57'])).
% 0.91/1.11  thf(commutativity_k2_xboole_0, axiom,
% 0.91/1.11    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.91/1.11  thf('59', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.11      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.91/1.11  thf('60', plain,
% 0.91/1.11      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.91/1.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.11  thf('61', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.11      inference('sup+', [status(thm)], ['28', '29'])).
% 0.91/1.11  thf('62', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.91/1.11  thf('63', plain,
% 0.91/1.11      (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.91/1.11      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.91/1.11  thf(t70_enumset1, axiom,
% 0.91/1.11    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.91/1.11  thf('64', plain,
% 0.91/1.11      (![X35 : $i, X36 : $i]:
% 0.91/1.11         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.91/1.11      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.91/1.11  thf(d1_enumset1, axiom,
% 0.91/1.11    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.11     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.91/1.11       ( ![E:$i]:
% 0.91/1.11         ( ( r2_hidden @ E @ D ) <=>
% 0.91/1.11           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.91/1.11  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.91/1.11  thf(zf_stmt_2, axiom,
% 0.91/1.11    (![E:$i,C:$i,B:$i,A:$i]:
% 0.91/1.11     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.91/1.11       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.91/1.11  thf(zf_stmt_3, axiom,
% 0.91/1.11    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.11     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.91/1.11       ( ![E:$i]:
% 0.91/1.11         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.91/1.11  thf('65', plain,
% 0.91/1.11      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.91/1.11         ((zip_tseitin_0 @ X27 @ X28 @ X29 @ X30)
% 0.91/1.11          | (r2_hidden @ X27 @ X31)
% 0.91/1.11          | ((X31) != (k1_enumset1 @ X30 @ X29 @ X28)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.11  thf('66', plain,
% 0.91/1.11      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.91/1.11         ((r2_hidden @ X27 @ (k1_enumset1 @ X30 @ X29 @ X28))
% 0.91/1.11          | (zip_tseitin_0 @ X27 @ X28 @ X29 @ X30))),
% 0.91/1.11      inference('simplify', [status(thm)], ['65'])).
% 0.91/1.11  thf('67', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.11         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.91/1.11          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.91/1.11      inference('sup+', [status(thm)], ['64', '66'])).
% 0.91/1.11  thf('68', plain,
% 0.91/1.11      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.91/1.11         (((X23) != (X22)) | ~ (zip_tseitin_0 @ X23 @ X24 @ X25 @ X22))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.91/1.11  thf('69', plain,
% 0.91/1.11      (![X22 : $i, X24 : $i, X25 : $i]:
% 0.91/1.11         ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X22)),
% 0.91/1.11      inference('simplify', [status(thm)], ['68'])).
% 0.91/1.11  thf('70', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.91/1.11      inference('sup-', [status(thm)], ['67', '69'])).
% 0.91/1.11  thf('71', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.91/1.11      inference('sup+', [status(thm)], ['63', '70'])).
% 0.91/1.11  thf('72', plain,
% 0.91/1.11      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.91/1.11         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.91/1.11      inference('simplify', [status(thm)], ['10'])).
% 0.91/1.11  thf('73', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['71', '72'])).
% 0.91/1.11  thf('74', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.91/1.11      inference('sup+', [status(thm)], ['62', '73'])).
% 0.91/1.11  thf('75', plain, ($false), inference('demod', [status(thm)], ['42', '74'])).
% 0.91/1.11  
% 0.91/1.11  % SZS output end Refutation
% 0.91/1.11  
% 0.91/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
