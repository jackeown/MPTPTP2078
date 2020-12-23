%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D7KYhlCEXW

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:29 EST 2020

% Result     : Theorem 3.59s
% Output     : Refutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 223 expanded)
%              Number of leaves         :   26 (  80 expanded)
%              Depth                    :   21
%              Number of atoms          :  805 (1693 expanded)
%              Number of equality atoms :   46 (  79 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) )
        = X39 )
      | ( r2_hidden @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ X28 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ( r1_xboole_0 @ X20 @ X21 )
      | ~ ( r1_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
      | ~ ( r1_xboole_0 @ X20 @ X21 )
      | ~ ( r1_xboole_0 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
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

thf('17',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['10','19'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('22',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ X28 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t77_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ X24 @ ( k3_xboole_0 @ X25 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k1_tarski @ sk_D ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('29',plain,(
    ! [X19: $i] :
      ( r1_xboole_0 @ X19 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('30',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_tarski @ sk_D ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','31','32','33'])).

thf('35',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['3','34'])).

thf('36',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('37',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('43',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['39','48'])).

thf('50',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ X28 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ X24 @ X25 )
      | ~ ( r1_xboole_0 @ X24 @ ( k3_xboole_0 @ X25 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X19: $i] :
      ( r1_xboole_0 @ X19 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['52','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['49','62'])).

thf('64',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('73',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('75',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('77',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('80',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['70','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('85',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
      | ~ ( r1_xboole_0 @ X20 @ X21 )
      | ~ ( r1_xboole_0 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X2 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_B ) @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['67','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('90',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['88','93'])).

thf('95',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('96',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['0','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D7KYhlCEXW
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:17:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.59/3.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.59/3.83  % Solved by: fo/fo7.sh
% 3.59/3.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.59/3.83  % done 5361 iterations in 3.346s
% 3.59/3.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.59/3.83  % SZS output start Refutation
% 3.59/3.83  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.59/3.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.59/3.83  thf(sk_D_type, type, sk_D: $i).
% 3.59/3.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.59/3.83  thf(sk_A_type, type, sk_A: $i).
% 3.59/3.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.59/3.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.59/3.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.59/3.83  thf(sk_B_type, type, sk_B: $i).
% 3.59/3.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.59/3.83  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.59/3.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.59/3.83  thf(t149_zfmisc_1, conjecture,
% 3.59/3.83    (![A:$i,B:$i,C:$i,D:$i]:
% 3.59/3.83     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 3.59/3.83         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 3.59/3.83       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 3.59/3.83  thf(zf_stmt_0, negated_conjecture,
% 3.59/3.83    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.59/3.83        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 3.59/3.83            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 3.59/3.83          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 3.59/3.83    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 3.59/3.83  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 3.59/3.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.59/3.83  thf('1', plain,
% 3.59/3.83      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 3.59/3.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.59/3.83  thf(commutativity_k3_xboole_0, axiom,
% 3.59/3.83    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.59/3.83  thf('2', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.59/3.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.59/3.83  thf('3', plain,
% 3.59/3.83      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 3.59/3.83      inference('demod', [status(thm)], ['1', '2'])).
% 3.59/3.83  thf(t65_zfmisc_1, axiom,
% 3.59/3.83    (![A:$i,B:$i]:
% 3.59/3.83     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 3.59/3.83       ( ~( r2_hidden @ B @ A ) ) ))).
% 3.59/3.83  thf('4', plain,
% 3.59/3.83      (![X39 : $i, X40 : $i]:
% 3.59/3.83         (((k4_xboole_0 @ X39 @ (k1_tarski @ X40)) = (X39))
% 3.59/3.83          | (r2_hidden @ X40 @ X39))),
% 3.59/3.83      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 3.59/3.83  thf(t79_xboole_1, axiom,
% 3.59/3.83    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 3.59/3.83  thf('5', plain,
% 3.59/3.83      (![X27 : $i, X28 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ X28)),
% 3.59/3.83      inference('cnf', [status(esa)], [t79_xboole_1])).
% 3.59/3.83  thf(symmetry_r1_xboole_0, axiom,
% 3.59/3.83    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 3.59/3.83  thf('6', plain,
% 3.59/3.83      (![X5 : $i, X6 : $i]:
% 3.59/3.83         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 3.59/3.83      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 3.59/3.83  thf('7', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 3.59/3.83      inference('sup-', [status(thm)], ['5', '6'])).
% 3.59/3.83  thf('8', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i]:
% 3.59/3.83         ((r1_xboole_0 @ (k1_tarski @ X1) @ X0) | (r2_hidden @ X1 @ X0))),
% 3.59/3.83      inference('sup+', [status(thm)], ['4', '7'])).
% 3.59/3.83  thf(t70_xboole_1, axiom,
% 3.59/3.83    (![A:$i,B:$i,C:$i]:
% 3.59/3.83     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 3.59/3.83            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 3.59/3.83       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 3.59/3.83            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 3.59/3.83  thf('9', plain,
% 3.59/3.83      (![X20 : $i, X21 : $i, X23 : $i]:
% 3.59/3.83         ((r1_xboole_0 @ X20 @ X21)
% 3.59/3.83          | ~ (r1_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X23)))),
% 3.59/3.83      inference('cnf', [status(esa)], [t70_xboole_1])).
% 3.59/3.83  thf('10', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.83         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 3.59/3.83          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 3.59/3.83      inference('sup-', [status(thm)], ['8', '9'])).
% 3.59/3.83  thf('11', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 3.59/3.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.59/3.83  thf('12', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 3.59/3.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.59/3.83  thf('13', plain,
% 3.59/3.83      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.59/3.83         ((r1_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 3.59/3.83          | ~ (r1_xboole_0 @ X20 @ X21)
% 3.59/3.83          | ~ (r1_xboole_0 @ X20 @ X22))),
% 3.59/3.83      inference('cnf', [status(esa)], [t70_xboole_1])).
% 3.59/3.83  thf('14', plain,
% 3.59/3.83      (![X0 : $i]:
% 3.59/3.83         (~ (r1_xboole_0 @ sk_C_1 @ X0)
% 3.59/3.83          | (r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 3.59/3.83      inference('sup-', [status(thm)], ['12', '13'])).
% 3.59/3.83  thf('15', plain, ((r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 3.59/3.83      inference('sup-', [status(thm)], ['11', '14'])).
% 3.59/3.83  thf('16', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 3.59/3.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.59/3.83  thf(t3_xboole_0, axiom,
% 3.59/3.83    (![A:$i,B:$i]:
% 3.59/3.83     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 3.59/3.83            ( r1_xboole_0 @ A @ B ) ) ) & 
% 3.59/3.83       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 3.59/3.83            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 3.59/3.83  thf('17', plain,
% 3.59/3.83      (![X7 : $i, X9 : $i, X10 : $i]:
% 3.59/3.83         (~ (r2_hidden @ X9 @ X7)
% 3.59/3.83          | ~ (r2_hidden @ X9 @ X10)
% 3.59/3.83          | ~ (r1_xboole_0 @ X7 @ X10))),
% 3.59/3.83      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.59/3.83  thf('18', plain,
% 3.59/3.83      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 3.59/3.83      inference('sup-', [status(thm)], ['16', '17'])).
% 3.59/3.83  thf('19', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ sk_B))),
% 3.59/3.83      inference('sup-', [status(thm)], ['15', '18'])).
% 3.59/3.83  thf('20', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 3.59/3.83      inference('sup-', [status(thm)], ['10', '19'])).
% 3.59/3.83  thf(d7_xboole_0, axiom,
% 3.59/3.83    (![A:$i,B:$i]:
% 3.59/3.83     ( ( r1_xboole_0 @ A @ B ) <=>
% 3.59/3.83       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 3.59/3.83  thf('21', plain,
% 3.59/3.83      (![X2 : $i, X3 : $i]:
% 3.59/3.83         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 3.59/3.83      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.59/3.83  thf('22', plain,
% 3.59/3.83      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) = (k1_xboole_0))),
% 3.59/3.83      inference('sup-', [status(thm)], ['20', '21'])).
% 3.59/3.83  thf('23', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.59/3.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.59/3.83  thf('24', plain,
% 3.59/3.83      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (k1_xboole_0))),
% 3.59/3.83      inference('demod', [status(thm)], ['22', '23'])).
% 3.59/3.83  thf('25', plain,
% 3.59/3.83      (![X27 : $i, X28 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ X28)),
% 3.59/3.83      inference('cnf', [status(esa)], [t79_xboole_1])).
% 3.59/3.83  thf(t77_xboole_1, axiom,
% 3.59/3.83    (![A:$i,B:$i,C:$i]:
% 3.59/3.83     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 3.59/3.83          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 3.59/3.83  thf('26', plain,
% 3.59/3.83      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.59/3.83         ((r1_xboole_0 @ X24 @ X25)
% 3.59/3.83          | ~ (r1_xboole_0 @ X24 @ (k3_xboole_0 @ X25 @ X26))
% 3.59/3.83          | ~ (r1_tarski @ X24 @ X26))),
% 3.59/3.83      inference('cnf', [status(esa)], [t77_xboole_1])).
% 3.59/3.83  thf('27', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.83         (~ (r1_tarski @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 3.59/3.83          | (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 3.59/3.83      inference('sup-', [status(thm)], ['25', '26'])).
% 3.59/3.83  thf('28', plain,
% 3.59/3.83      (![X0 : $i]:
% 3.59/3.83         (~ (r1_tarski @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ (k1_tarski @ sk_D))
% 3.59/3.83          | (r1_xboole_0 @ 
% 3.59/3.83             (k4_xboole_0 @ X0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D))) @ 
% 3.59/3.83             sk_B))),
% 3.59/3.83      inference('sup-', [status(thm)], ['24', '27'])).
% 3.59/3.83  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 3.59/3.83  thf('29', plain, (![X19 : $i]: (r1_xboole_0 @ X19 @ k1_xboole_0)),
% 3.59/3.83      inference('cnf', [status(esa)], [t65_xboole_1])).
% 3.59/3.83  thf(t83_xboole_1, axiom,
% 3.59/3.83    (![A:$i,B:$i]:
% 3.59/3.83     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.59/3.83  thf('30', plain,
% 3.59/3.83      (![X29 : $i, X30 : $i]:
% 3.59/3.83         (((k4_xboole_0 @ X29 @ X30) = (X29)) | ~ (r1_xboole_0 @ X29 @ X30))),
% 3.59/3.83      inference('cnf', [status(esa)], [t83_xboole_1])).
% 3.59/3.83  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.59/3.83      inference('sup-', [status(thm)], ['29', '30'])).
% 3.59/3.83  thf('32', plain,
% 3.59/3.83      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (k1_xboole_0))),
% 3.59/3.83      inference('demod', [status(thm)], ['22', '23'])).
% 3.59/3.83  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.59/3.83      inference('sup-', [status(thm)], ['29', '30'])).
% 3.59/3.83  thf('34', plain,
% 3.59/3.83      (![X0 : $i]:
% 3.59/3.83         (~ (r1_tarski @ X0 @ (k1_tarski @ sk_D)) | (r1_xboole_0 @ X0 @ sk_B))),
% 3.59/3.83      inference('demod', [status(thm)], ['28', '31', '32', '33'])).
% 3.59/3.83  thf('35', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 3.59/3.83      inference('sup-', [status(thm)], ['3', '34'])).
% 3.59/3.83  thf('36', plain,
% 3.59/3.83      (![X5 : $i, X6 : $i]:
% 3.59/3.83         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 3.59/3.83      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 3.59/3.83  thf('37', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A))),
% 3.59/3.83      inference('sup-', [status(thm)], ['35', '36'])).
% 3.59/3.83  thf('38', plain,
% 3.59/3.83      (![X29 : $i, X30 : $i]:
% 3.59/3.83         (((k4_xboole_0 @ X29 @ X30) = (X29)) | ~ (r1_xboole_0 @ X29 @ X30))),
% 3.59/3.83      inference('cnf', [status(esa)], [t83_xboole_1])).
% 3.59/3.83  thf('39', plain,
% 3.59/3.83      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 3.59/3.83      inference('sup-', [status(thm)], ['37', '38'])).
% 3.59/3.83  thf(t48_xboole_1, axiom,
% 3.59/3.83    (![A:$i,B:$i]:
% 3.59/3.83     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.59/3.83  thf('40', plain,
% 3.59/3.83      (![X17 : $i, X18 : $i]:
% 3.59/3.83         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 3.59/3.83           = (k3_xboole_0 @ X17 @ X18))),
% 3.59/3.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.59/3.83  thf('41', plain,
% 3.59/3.83      (![X17 : $i, X18 : $i]:
% 3.59/3.83         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 3.59/3.83           = (k3_xboole_0 @ X17 @ X18))),
% 3.59/3.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.59/3.83  thf('42', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i]:
% 3.59/3.83         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 3.59/3.83           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.59/3.83      inference('sup+', [status(thm)], ['40', '41'])).
% 3.59/3.83  thf(t36_xboole_1, axiom,
% 3.59/3.83    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 3.59/3.83  thf('43', plain,
% 3.59/3.83      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 3.59/3.83      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.59/3.83  thf(t28_xboole_1, axiom,
% 3.59/3.83    (![A:$i,B:$i]:
% 3.59/3.83     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.59/3.83  thf('44', plain,
% 3.59/3.83      (![X13 : $i, X14 : $i]:
% 3.59/3.83         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 3.59/3.83      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.59/3.83  thf('45', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i]:
% 3.59/3.83         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 3.59/3.83           = (k4_xboole_0 @ X0 @ X1))),
% 3.59/3.83      inference('sup-', [status(thm)], ['43', '44'])).
% 3.59/3.83  thf('46', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.59/3.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.59/3.83  thf('47', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i]:
% 3.59/3.83         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 3.59/3.83           = (k4_xboole_0 @ X0 @ X1))),
% 3.59/3.83      inference('demod', [status(thm)], ['45', '46'])).
% 3.59/3.83  thf('48', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i]:
% 3.59/3.83         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 3.59/3.83           = (k4_xboole_0 @ X1 @ X0))),
% 3.59/3.83      inference('demod', [status(thm)], ['42', '47'])).
% 3.59/3.83  thf('49', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 3.59/3.83      inference('demod', [status(thm)], ['39', '48'])).
% 3.59/3.83  thf('50', plain,
% 3.59/3.83      (![X17 : $i, X18 : $i]:
% 3.59/3.83         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 3.59/3.83           = (k3_xboole_0 @ X17 @ X18))),
% 3.59/3.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.59/3.83  thf('51', plain,
% 3.59/3.83      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 3.59/3.83      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.59/3.83  thf('52', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 3.59/3.83      inference('sup+', [status(thm)], ['50', '51'])).
% 3.59/3.83  thf('53', plain,
% 3.59/3.83      (![X27 : $i, X28 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ X28)),
% 3.59/3.83      inference('cnf', [status(esa)], [t79_xboole_1])).
% 3.59/3.83  thf('54', plain,
% 3.59/3.83      (![X2 : $i, X3 : $i]:
% 3.59/3.83         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 3.59/3.83      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.59/3.83  thf('55', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i]:
% 3.59/3.83         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 3.59/3.83      inference('sup-', [status(thm)], ['53', '54'])).
% 3.59/3.83  thf('56', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.59/3.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.59/3.83  thf('57', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i]:
% 3.59/3.83         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 3.59/3.83      inference('demod', [status(thm)], ['55', '56'])).
% 3.59/3.83  thf('58', plain,
% 3.59/3.83      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.59/3.83         ((r1_xboole_0 @ X24 @ X25)
% 3.59/3.83          | ~ (r1_xboole_0 @ X24 @ (k3_xboole_0 @ X25 @ X26))
% 3.59/3.83          | ~ (r1_tarski @ X24 @ X26))),
% 3.59/3.83      inference('cnf', [status(esa)], [t77_xboole_1])).
% 3.59/3.83  thf('59', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.83         (~ (r1_xboole_0 @ X2 @ k1_xboole_0)
% 3.59/3.83          | ~ (r1_tarski @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 3.59/3.83          | (r1_xboole_0 @ X2 @ X0))),
% 3.59/3.83      inference('sup-', [status(thm)], ['57', '58'])).
% 3.59/3.83  thf('60', plain, (![X19 : $i]: (r1_xboole_0 @ X19 @ k1_xboole_0)),
% 3.59/3.83      inference('cnf', [status(esa)], [t65_xboole_1])).
% 3.59/3.83  thf('61', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.83         (~ (r1_tarski @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 3.59/3.83          | (r1_xboole_0 @ X2 @ X0))),
% 3.59/3.83      inference('demod', [status(thm)], ['59', '60'])).
% 3.59/3.83  thf('62', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.83         (r1_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0)),
% 3.59/3.83      inference('sup-', [status(thm)], ['52', '61'])).
% 3.59/3.83  thf('63', plain,
% 3.59/3.83      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)),
% 3.59/3.83      inference('sup+', [status(thm)], ['49', '62'])).
% 3.59/3.83  thf('64', plain,
% 3.59/3.83      (![X5 : $i, X6 : $i]:
% 3.59/3.83         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 3.59/3.83      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 3.59/3.83  thf('65', plain,
% 3.59/3.83      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))),
% 3.59/3.83      inference('sup-', [status(thm)], ['63', '64'])).
% 3.59/3.83  thf('66', plain,
% 3.59/3.83      (![X29 : $i, X30 : $i]:
% 3.59/3.83         (((k4_xboole_0 @ X29 @ X30) = (X29)) | ~ (r1_xboole_0 @ X29 @ X30))),
% 3.59/3.83      inference('cnf', [status(esa)], [t83_xboole_1])).
% 3.59/3.83  thf('67', plain,
% 3.59/3.83      (![X0 : $i]: ((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) = (sk_A))),
% 3.59/3.83      inference('sup-', [status(thm)], ['65', '66'])).
% 3.59/3.83  thf('68', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.59/3.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.59/3.83  thf('69', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 3.59/3.83      inference('sup+', [status(thm)], ['50', '51'])).
% 3.59/3.83  thf('70', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 3.59/3.83      inference('sup+', [status(thm)], ['68', '69'])).
% 3.59/3.83  thf('71', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 3.59/3.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.59/3.83  thf('72', plain,
% 3.59/3.83      (![X2 : $i, X3 : $i]:
% 3.59/3.83         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 3.59/3.83      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.59/3.83  thf('73', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 3.59/3.83      inference('sup-', [status(thm)], ['71', '72'])).
% 3.59/3.83  thf('74', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.59/3.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.59/3.83  thf('75', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 3.59/3.83      inference('demod', [status(thm)], ['73', '74'])).
% 3.59/3.83  thf('76', plain,
% 3.59/3.83      (![X2 : $i, X4 : $i]:
% 3.59/3.83         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 3.59/3.83      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.59/3.83  thf('77', plain,
% 3.59/3.83      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_1))),
% 3.59/3.83      inference('sup-', [status(thm)], ['75', '76'])).
% 3.59/3.83  thf('78', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 3.59/3.83      inference('simplify', [status(thm)], ['77'])).
% 3.59/3.83  thf('79', plain,
% 3.59/3.83      (![X29 : $i, X30 : $i]:
% 3.59/3.83         (((k4_xboole_0 @ X29 @ X30) = (X29)) | ~ (r1_xboole_0 @ X29 @ X30))),
% 3.59/3.83      inference('cnf', [status(esa)], [t83_xboole_1])).
% 3.59/3.83  thf('80', plain, (((k4_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 3.59/3.83      inference('sup-', [status(thm)], ['78', '79'])).
% 3.59/3.83  thf('81', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.83         (~ (r1_tarski @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 3.59/3.83          | (r1_xboole_0 @ X2 @ X0))),
% 3.59/3.83      inference('demod', [status(thm)], ['59', '60'])).
% 3.59/3.83  thf('82', plain,
% 3.59/3.83      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_B) | (r1_xboole_0 @ X0 @ sk_C_1))),
% 3.59/3.83      inference('sup-', [status(thm)], ['80', '81'])).
% 3.59/3.83  thf('83', plain,
% 3.59/3.83      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_C_1)),
% 3.59/3.83      inference('sup-', [status(thm)], ['70', '82'])).
% 3.59/3.83  thf('84', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 3.59/3.83      inference('sup-', [status(thm)], ['5', '6'])).
% 3.59/3.83  thf('85', plain,
% 3.59/3.83      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.59/3.83         ((r1_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 3.59/3.83          | ~ (r1_xboole_0 @ X20 @ X21)
% 3.59/3.83          | ~ (r1_xboole_0 @ X20 @ X22))),
% 3.59/3.83      inference('cnf', [status(esa)], [t70_xboole_1])).
% 3.59/3.83  thf('86', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.59/3.83         (~ (r1_xboole_0 @ X0 @ X2)
% 3.59/3.83          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 3.59/3.83      inference('sup-', [status(thm)], ['84', '85'])).
% 3.59/3.83  thf('87', plain,
% 3.59/3.83      (![X0 : $i, X1 : $i]:
% 3.59/3.83         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 3.59/3.83          (k2_xboole_0 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 3.59/3.83           sk_C_1))),
% 3.59/3.83      inference('sup-', [status(thm)], ['83', '86'])).
% 3.59/3.83  thf('88', plain,
% 3.59/3.83      ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_B) @ 
% 3.59/3.83        (k2_xboole_0 @ sk_A @ sk_C_1))),
% 3.59/3.83      inference('sup+', [status(thm)], ['67', '87'])).
% 3.59/3.83  thf('89', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.59/3.83      inference('sup-', [status(thm)], ['29', '30'])).
% 3.59/3.83  thf('90', plain,
% 3.59/3.83      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 3.59/3.83      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.59/3.83  thf('91', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 3.59/3.83      inference('sup+', [status(thm)], ['89', '90'])).
% 3.59/3.83  thf('92', plain,
% 3.59/3.83      (![X13 : $i, X14 : $i]:
% 3.59/3.83         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 3.59/3.83      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.59/3.83  thf('93', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 3.59/3.83      inference('sup-', [status(thm)], ['91', '92'])).
% 3.59/3.83  thf('94', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 3.59/3.83      inference('demod', [status(thm)], ['88', '93'])).
% 3.59/3.83  thf('95', plain,
% 3.59/3.83      (![X5 : $i, X6 : $i]:
% 3.59/3.83         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 3.59/3.83      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 3.59/3.83  thf('96', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 3.59/3.83      inference('sup-', [status(thm)], ['94', '95'])).
% 3.59/3.83  thf('97', plain, ($false), inference('demod', [status(thm)], ['0', '96'])).
% 3.59/3.83  
% 3.59/3.83  % SZS output end Refutation
% 3.59/3.83  
% 3.59/3.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
