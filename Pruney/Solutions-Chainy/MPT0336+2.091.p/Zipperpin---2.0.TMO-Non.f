%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ohswa6VksF

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:32 EST 2020

% Result     : Timeout 59.93s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  117 ( 472 expanded)
%              Number of leaves         :   28 ( 168 expanded)
%              Depth                    :   19
%              Number of atoms          :  817 (3572 expanded)
%              Number of equality atoms :   69 ( 355 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k4_xboole_0 @ X38 @ ( k1_tarski @ X39 ) )
        = X38 )
      | ( r2_hidden @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('5',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('23',plain,(
    ! [X25: $i] :
      ( r1_xboole_0 @ X25 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('24',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X34 @ X35 ) @ X35 )
        = X34 )
      | ~ ( r1_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('29',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','27','28'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ) ),
    inference('sup+',[status(thm)],['11','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','31'])).

thf('39',plain,(
    ! [X25: $i] :
      ( r1_xboole_0 @ X25 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X34 @ X35 ) @ X35 )
        = X34 )
      | ~ ( r1_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X25: $i] :
      ( r1_xboole_0 @ X25 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('45',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t72_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf('46',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X31 = X30 )
      | ~ ( r1_xboole_0 @ X31 @ X32 )
      | ( ( k2_xboole_0 @ X32 @ X30 )
       != ( k2_xboole_0 @ X31 @ X33 ) )
      | ~ ( r1_xboole_0 @ X33 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t72_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
       != X0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
       != X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
        = X1 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','31'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('58',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['34','37','38','56','57'])).

thf('59',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['4','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('61',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    r2_hidden @ sk_D @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('64',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('69',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','27','28'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf('77',plain,
    ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['61','66'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('81',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('82',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r1_xboole_0 @ X26 @ ( k2_xboole_0 @ X27 @ X28 ) )
      | ~ ( r1_xboole_0 @ X26 @ X27 )
      | ~ ( r1_xboole_0 @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','83'])).

thf('85',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('86',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['0','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ohswa6VksF
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 59.93/60.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 59.93/60.14  % Solved by: fo/fo7.sh
% 59.93/60.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 59.93/60.14  % done 48612 iterations in 59.682s
% 59.93/60.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 59.93/60.14  % SZS output start Refutation
% 59.93/60.14  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 59.93/60.14  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 59.93/60.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 59.93/60.14  thf(sk_A_type, type, sk_A: $i).
% 59.93/60.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 59.93/60.14  thf(sk_B_type, type, sk_B: $i).
% 59.93/60.14  thf(sk_C_2_type, type, sk_C_2: $i).
% 59.93/60.14  thf(sk_D_type, type, sk_D: $i).
% 59.93/60.14  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 59.93/60.14  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 59.93/60.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 59.93/60.14  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 59.93/60.14  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 59.93/60.14  thf(t149_zfmisc_1, conjecture,
% 59.93/60.14    (![A:$i,B:$i,C:$i,D:$i]:
% 59.93/60.14     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 59.93/60.14         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 59.93/60.14       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 59.93/60.14  thf(zf_stmt_0, negated_conjecture,
% 59.93/60.14    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 59.93/60.14        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 59.93/60.14            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 59.93/60.14          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 59.93/60.14    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 59.93/60.14  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 59.93/60.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.93/60.14  thf('1', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 59.93/60.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.93/60.14  thf(symmetry_r1_xboole_0, axiom,
% 59.93/60.14    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 59.93/60.14  thf('2', plain,
% 59.93/60.14      (![X2 : $i, X3 : $i]:
% 59.93/60.14         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 59.93/60.14      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 59.93/60.14  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 59.93/60.14      inference('sup-', [status(thm)], ['1', '2'])).
% 59.93/60.14  thf(t65_zfmisc_1, axiom,
% 59.93/60.14    (![A:$i,B:$i]:
% 59.93/60.14     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 59.93/60.14       ( ~( r2_hidden @ B @ A ) ) ))).
% 59.93/60.14  thf('4', plain,
% 59.93/60.14      (![X38 : $i, X39 : $i]:
% 59.93/60.14         (((k4_xboole_0 @ X38 @ (k1_tarski @ X39)) = (X38))
% 59.93/60.14          | (r2_hidden @ X39 @ X38))),
% 59.93/60.14      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 59.93/60.14  thf('5', plain,
% 59.93/60.14      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 59.93/60.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.93/60.14  thf(commutativity_k3_xboole_0, axiom,
% 59.93/60.14    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 59.93/60.14  thf('6', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 59.93/60.14      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 59.93/60.14  thf('7', plain,
% 59.93/60.14      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 59.93/60.14      inference('demod', [status(thm)], ['5', '6'])).
% 59.93/60.14  thf(t28_xboole_1, axiom,
% 59.93/60.14    (![A:$i,B:$i]:
% 59.93/60.14     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 59.93/60.14  thf('8', plain,
% 59.93/60.14      (![X13 : $i, X14 : $i]:
% 59.93/60.14         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 59.93/60.14      inference('cnf', [status(esa)], [t28_xboole_1])).
% 59.93/60.14  thf('9', plain,
% 59.93/60.14      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 59.93/60.14         = (k3_xboole_0 @ sk_B @ sk_A))),
% 59.93/60.14      inference('sup-', [status(thm)], ['7', '8'])).
% 59.93/60.14  thf('10', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 59.93/60.14      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 59.93/60.14  thf('11', plain,
% 59.93/60.14      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 59.93/60.14         = (k3_xboole_0 @ sk_B @ sk_A))),
% 59.93/60.14      inference('demod', [status(thm)], ['9', '10'])).
% 59.93/60.14  thf('12', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 59.93/60.14      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 59.93/60.14  thf(t48_xboole_1, axiom,
% 59.93/60.14    (![A:$i,B:$i]:
% 59.93/60.14     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 59.93/60.14  thf('13', plain,
% 59.93/60.14      (![X16 : $i, X17 : $i]:
% 59.93/60.14         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 59.93/60.14           = (k3_xboole_0 @ X16 @ X17))),
% 59.93/60.14      inference('cnf', [status(esa)], [t48_xboole_1])).
% 59.93/60.14  thf('14', plain,
% 59.93/60.14      (![X16 : $i, X17 : $i]:
% 59.93/60.14         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 59.93/60.14           = (k3_xboole_0 @ X16 @ X17))),
% 59.93/60.14      inference('cnf', [status(esa)], [t48_xboole_1])).
% 59.93/60.14  thf('15', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]:
% 59.93/60.14         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 59.93/60.14           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 59.93/60.14      inference('sup+', [status(thm)], ['13', '14'])).
% 59.93/60.14  thf('16', plain,
% 59.93/60.14      (![X16 : $i, X17 : $i]:
% 59.93/60.14         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 59.93/60.14           = (k3_xboole_0 @ X16 @ X17))),
% 59.93/60.14      inference('cnf', [status(esa)], [t48_xboole_1])).
% 59.93/60.14  thf(t4_boole, axiom,
% 59.93/60.14    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 59.93/60.14  thf('17', plain,
% 59.93/60.14      (![X21 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X21) = (k1_xboole_0))),
% 59.93/60.14      inference('cnf', [status(esa)], [t4_boole])).
% 59.93/60.14  thf('18', plain,
% 59.93/60.14      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 59.93/60.14      inference('sup+', [status(thm)], ['16', '17'])).
% 59.93/60.14  thf('19', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 59.93/60.14      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 59.93/60.14  thf('20', plain,
% 59.93/60.14      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 59.93/60.14      inference('sup+', [status(thm)], ['18', '19'])).
% 59.93/60.14  thf('21', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]:
% 59.93/60.14         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 59.93/60.14           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 59.93/60.14      inference('sup+', [status(thm)], ['13', '14'])).
% 59.93/60.14  thf('22', plain,
% 59.93/60.14      (![X0 : $i]:
% 59.93/60.14         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 59.93/60.14           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 59.93/60.14      inference('sup+', [status(thm)], ['20', '21'])).
% 59.93/60.14  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 59.93/60.14  thf('23', plain, (![X25 : $i]: (r1_xboole_0 @ X25 @ k1_xboole_0)),
% 59.93/60.14      inference('cnf', [status(esa)], [t65_xboole_1])).
% 59.93/60.14  thf(t88_xboole_1, axiom,
% 59.93/60.14    (![A:$i,B:$i]:
% 59.93/60.14     ( ( r1_xboole_0 @ A @ B ) =>
% 59.93/60.14       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 59.93/60.14  thf('24', plain,
% 59.93/60.14      (![X34 : $i, X35 : $i]:
% 59.93/60.14         (((k4_xboole_0 @ (k2_xboole_0 @ X34 @ X35) @ X35) = (X34))
% 59.93/60.14          | ~ (r1_xboole_0 @ X34 @ X35))),
% 59.93/60.14      inference('cnf', [status(esa)], [t88_xboole_1])).
% 59.93/60.14  thf('25', plain,
% 59.93/60.14      (![X0 : $i]:
% 59.93/60.14         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0) = (X0))),
% 59.93/60.14      inference('sup-', [status(thm)], ['23', '24'])).
% 59.93/60.14  thf(t1_boole, axiom,
% 59.93/60.14    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 59.93/60.14  thf('26', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 59.93/60.14      inference('cnf', [status(esa)], [t1_boole])).
% 59.93/60.14  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 59.93/60.14      inference('demod', [status(thm)], ['25', '26'])).
% 59.93/60.14  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 59.93/60.14      inference('demod', [status(thm)], ['25', '26'])).
% 59.93/60.14  thf('29', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 59.93/60.14      inference('demod', [status(thm)], ['22', '27', '28'])).
% 59.93/60.14  thf(t49_xboole_1, axiom,
% 59.93/60.14    (![A:$i,B:$i,C:$i]:
% 59.93/60.14     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 59.93/60.14       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 59.93/60.14  thf('30', plain,
% 59.93/60.14      (![X18 : $i, X19 : $i, X20 : $i]:
% 59.93/60.14         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 59.93/60.14           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 59.93/60.14      inference('cnf', [status(esa)], [t49_xboole_1])).
% 59.93/60.14  thf('31', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]:
% 59.93/60.14         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 59.93/60.14           = (k4_xboole_0 @ X0 @ X1))),
% 59.93/60.14      inference('sup+', [status(thm)], ['29', '30'])).
% 59.93/60.14  thf('32', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]:
% 59.93/60.14         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 59.93/60.14           = (k4_xboole_0 @ X1 @ X0))),
% 59.93/60.14      inference('demod', [status(thm)], ['15', '31'])).
% 59.93/60.14  thf('33', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]:
% 59.93/60.14         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 59.93/60.14           = (k4_xboole_0 @ X0 @ X1))),
% 59.93/60.14      inference('sup+', [status(thm)], ['12', '32'])).
% 59.93/60.14  thf('34', plain,
% 59.93/60.14      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 59.93/60.14         (k3_xboole_0 @ sk_B @ sk_A))
% 59.93/60.14         = (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D)))),
% 59.93/60.14      inference('sup+', [status(thm)], ['11', '33'])).
% 59.93/60.14  thf('35', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 59.93/60.14      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 59.93/60.14  thf('36', plain,
% 59.93/60.14      (![X18 : $i, X19 : $i, X20 : $i]:
% 59.93/60.14         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 59.93/60.14           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 59.93/60.14      inference('cnf', [status(esa)], [t49_xboole_1])).
% 59.93/60.14  thf('37', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.93/60.14         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 59.93/60.14           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 59.93/60.14      inference('sup+', [status(thm)], ['35', '36'])).
% 59.93/60.14  thf('38', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]:
% 59.93/60.14         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 59.93/60.14           = (k4_xboole_0 @ X1 @ X0))),
% 59.93/60.14      inference('demod', [status(thm)], ['15', '31'])).
% 59.93/60.14  thf('39', plain, (![X25 : $i]: (r1_xboole_0 @ X25 @ k1_xboole_0)),
% 59.93/60.14      inference('cnf', [status(esa)], [t65_xboole_1])).
% 59.93/60.14  thf('40', plain,
% 59.93/60.14      (![X2 : $i, X3 : $i]:
% 59.93/60.14         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 59.93/60.14      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 59.93/60.14  thf('41', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 59.93/60.14      inference('sup-', [status(thm)], ['39', '40'])).
% 59.93/60.14  thf('42', plain,
% 59.93/60.14      (![X34 : $i, X35 : $i]:
% 59.93/60.14         (((k4_xboole_0 @ (k2_xboole_0 @ X34 @ X35) @ X35) = (X34))
% 59.93/60.14          | ~ (r1_xboole_0 @ X34 @ X35))),
% 59.93/60.14      inference('cnf', [status(esa)], [t88_xboole_1])).
% 59.93/60.14  thf('43', plain,
% 59.93/60.14      (![X0 : $i]:
% 59.93/60.14         ((k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0) = (k1_xboole_0))),
% 59.93/60.14      inference('sup-', [status(thm)], ['41', '42'])).
% 59.93/60.14  thf('44', plain, (![X25 : $i]: (r1_xboole_0 @ X25 @ k1_xboole_0)),
% 59.93/60.14      inference('cnf', [status(esa)], [t65_xboole_1])).
% 59.93/60.14  thf('45', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 59.93/60.14      inference('cnf', [status(esa)], [t1_boole])).
% 59.93/60.14  thf(t72_xboole_1, axiom,
% 59.93/60.14    (![A:$i,B:$i,C:$i,D:$i]:
% 59.93/60.14     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 59.93/60.14         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 59.93/60.14       ( ( C ) = ( B ) ) ))).
% 59.93/60.14  thf('46', plain,
% 59.93/60.14      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 59.93/60.14         (((X31) = (X30))
% 59.93/60.14          | ~ (r1_xboole_0 @ X31 @ X32)
% 59.93/60.14          | ((k2_xboole_0 @ X32 @ X30) != (k2_xboole_0 @ X31 @ X33))
% 59.93/60.14          | ~ (r1_xboole_0 @ X33 @ X30))),
% 59.93/60.14      inference('cnf', [status(esa)], [t72_xboole_1])).
% 59.93/60.14  thf('47', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.93/60.14         (((k2_xboole_0 @ X2 @ X1) != (X0))
% 59.93/60.14          | ~ (r1_xboole_0 @ k1_xboole_0 @ X1)
% 59.93/60.14          | ~ (r1_xboole_0 @ X0 @ X2)
% 59.93/60.14          | ((X0) = (X1)))),
% 59.93/60.14      inference('sup-', [status(thm)], ['45', '46'])).
% 59.93/60.14  thf('48', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 59.93/60.14      inference('sup-', [status(thm)], ['39', '40'])).
% 59.93/60.14  thf('49', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.93/60.14         (((k2_xboole_0 @ X2 @ X1) != (X0))
% 59.93/60.14          | ~ (r1_xboole_0 @ X0 @ X2)
% 59.93/60.14          | ((X0) = (X1)))),
% 59.93/60.14      inference('demod', [status(thm)], ['47', '48'])).
% 59.93/60.14  thf('50', plain,
% 59.93/60.14      (![X1 : $i, X2 : $i]:
% 59.93/60.14         (((k2_xboole_0 @ X2 @ X1) = (X1))
% 59.93/60.14          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X2))),
% 59.93/60.14      inference('simplify', [status(thm)], ['49'])).
% 59.93/60.14  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 59.93/60.14      inference('sup-', [status(thm)], ['44', '50'])).
% 59.93/60.14  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 59.93/60.14      inference('demod', [status(thm)], ['43', '51'])).
% 59.93/60.14  thf('53', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.93/60.14         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 59.93/60.14           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 59.93/60.14      inference('sup+', [status(thm)], ['35', '36'])).
% 59.93/60.14  thf('54', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]:
% 59.93/60.14         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 59.93/60.14           = (k1_xboole_0))),
% 59.93/60.14      inference('sup+', [status(thm)], ['52', '53'])).
% 59.93/60.14  thf('55', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]:
% 59.93/60.14         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 59.93/60.14           = (k4_xboole_0 @ X1 @ X0))),
% 59.93/60.14      inference('demod', [status(thm)], ['15', '31'])).
% 59.93/60.14  thf('56', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]:
% 59.93/60.14         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 59.93/60.14      inference('demod', [status(thm)], ['54', '55'])).
% 59.93/60.14  thf('57', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.93/60.14         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 59.93/60.14           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 59.93/60.14      inference('sup+', [status(thm)], ['35', '36'])).
% 59.93/60.14  thf('58', plain,
% 59.93/60.14      (((k1_xboole_0)
% 59.93/60.14         = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D))))),
% 59.93/60.14      inference('demod', [status(thm)], ['34', '37', '38', '56', '57'])).
% 59.93/60.14  thf('59', plain,
% 59.93/60.14      ((((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))
% 59.93/60.14        | (r2_hidden @ sk_D @ sk_B))),
% 59.93/60.14      inference('sup+', [status(thm)], ['4', '58'])).
% 59.93/60.14  thf('60', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 59.93/60.14      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 59.93/60.14  thf('61', plain,
% 59.93/60.14      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))
% 59.93/60.14        | (r2_hidden @ sk_D @ sk_B))),
% 59.93/60.14      inference('demod', [status(thm)], ['59', '60'])).
% 59.93/60.14  thf('62', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 59.93/60.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.93/60.14  thf('63', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 59.93/60.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.93/60.14  thf(t3_xboole_0, axiom,
% 59.93/60.14    (![A:$i,B:$i]:
% 59.93/60.14     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 59.93/60.14            ( r1_xboole_0 @ A @ B ) ) ) & 
% 59.93/60.14       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 59.93/60.14            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 59.93/60.14  thf('64', plain,
% 59.93/60.14      (![X4 : $i, X6 : $i, X7 : $i]:
% 59.93/60.14         (~ (r2_hidden @ X6 @ X4)
% 59.93/60.14          | ~ (r2_hidden @ X6 @ X7)
% 59.93/60.14          | ~ (r1_xboole_0 @ X4 @ X7))),
% 59.93/60.14      inference('cnf', [status(esa)], [t3_xboole_0])).
% 59.93/60.14  thf('65', plain,
% 59.93/60.14      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 59.93/60.14      inference('sup-', [status(thm)], ['63', '64'])).
% 59.93/60.14  thf('66', plain, (~ (r2_hidden @ sk_D @ sk_B)),
% 59.93/60.14      inference('sup-', [status(thm)], ['62', '65'])).
% 59.93/60.14  thf('67', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 59.93/60.14      inference('clc', [status(thm)], ['61', '66'])).
% 59.93/60.14  thf('68', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 59.93/60.14      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 59.93/60.14  thf(t4_xboole_0, axiom,
% 59.93/60.14    (![A:$i,B:$i]:
% 59.93/60.14     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 59.93/60.14            ( r1_xboole_0 @ A @ B ) ) ) & 
% 59.93/60.14       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 59.93/60.14            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 59.93/60.14  thf('69', plain,
% 59.93/60.14      (![X8 : $i, X9 : $i]:
% 59.93/60.14         ((r1_xboole_0 @ X8 @ X9)
% 59.93/60.14          | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 59.93/60.14      inference('cnf', [status(esa)], [t4_xboole_0])).
% 59.93/60.14  thf('70', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 59.93/60.14      inference('demod', [status(thm)], ['22', '27', '28'])).
% 59.93/60.14  thf('71', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 59.93/60.14      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 59.93/60.14  thf('72', plain,
% 59.93/60.14      (![X8 : $i, X10 : $i, X11 : $i]:
% 59.93/60.14         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 59.93/60.14          | ~ (r1_xboole_0 @ X8 @ X11))),
% 59.93/60.14      inference('cnf', [status(esa)], [t4_xboole_0])).
% 59.93/60.14  thf('73', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.93/60.14         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 59.93/60.14          | ~ (r1_xboole_0 @ X0 @ X1))),
% 59.93/60.14      inference('sup-', [status(thm)], ['71', '72'])).
% 59.93/60.14  thf('74', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]:
% 59.93/60.14         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 59.93/60.14      inference('sup-', [status(thm)], ['70', '73'])).
% 59.93/60.14  thf('75', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]:
% 59.93/60.14         ((r1_xboole_0 @ X1 @ X0)
% 59.93/60.14          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 59.93/60.14      inference('sup-', [status(thm)], ['69', '74'])).
% 59.93/60.14  thf('76', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]:
% 59.93/60.14         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 59.93/60.14          | (r1_xboole_0 @ X0 @ X1))),
% 59.93/60.14      inference('sup-', [status(thm)], ['68', '75'])).
% 59.93/60.14  thf('77', plain,
% 59.93/60.14      ((~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)
% 59.93/60.14        | (r1_xboole_0 @ sk_B @ sk_A))),
% 59.93/60.14      inference('sup-', [status(thm)], ['67', '76'])).
% 59.93/60.14  thf('78', plain,
% 59.93/60.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 59.93/60.14      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 59.93/60.14  thf('79', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 59.93/60.14      inference('clc', [status(thm)], ['61', '66'])).
% 59.93/60.14  thf('80', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 59.93/60.14      inference('sup-', [status(thm)], ['39', '40'])).
% 59.93/60.14  thf('81', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 59.93/60.14      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 59.93/60.14  thf(t70_xboole_1, axiom,
% 59.93/60.14    (![A:$i,B:$i,C:$i]:
% 59.93/60.14     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 59.93/60.14            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 59.93/60.14       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 59.93/60.14            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 59.93/60.14  thf('82', plain,
% 59.93/60.14      (![X26 : $i, X27 : $i, X28 : $i]:
% 59.93/60.14         ((r1_xboole_0 @ X26 @ (k2_xboole_0 @ X27 @ X28))
% 59.93/60.14          | ~ (r1_xboole_0 @ X26 @ X27)
% 59.93/60.14          | ~ (r1_xboole_0 @ X26 @ X28))),
% 59.93/60.14      inference('cnf', [status(esa)], [t70_xboole_1])).
% 59.93/60.14  thf('83', plain,
% 59.93/60.14      (![X0 : $i]:
% 59.93/60.14         (~ (r1_xboole_0 @ sk_B @ X0)
% 59.93/60.14          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 59.93/60.14      inference('sup-', [status(thm)], ['81', '82'])).
% 59.93/60.14  thf('84', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_2))),
% 59.93/60.14      inference('sup-', [status(thm)], ['3', '83'])).
% 59.93/60.14  thf('85', plain,
% 59.93/60.14      (![X2 : $i, X3 : $i]:
% 59.93/60.14         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 59.93/60.14      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 59.93/60.14  thf('86', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 59.93/60.14      inference('sup-', [status(thm)], ['84', '85'])).
% 59.93/60.14  thf('87', plain, ($false), inference('demod', [status(thm)], ['0', '86'])).
% 59.93/60.14  
% 59.93/60.14  % SZS output end Refutation
% 59.93/60.14  
% 59.93/60.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
