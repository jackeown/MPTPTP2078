%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wcNbyE27Hj

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:27 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 121 expanded)
%              Number of leaves         :   23 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  581 ( 938 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf(t77_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ sk_C_2 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('11',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_C_2 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('15',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X30 ) @ X31 )
      | ( r2_hidden @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('16',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('20',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_C_2 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_C_2 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_2 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
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

thf('43',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['26','45'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('47',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X21 @ X22 )
      | ( ( k3_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
        = ( k3_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','59'])).

thf('61',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['13','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['0','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wcNbyE27Hj
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:26:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.38/1.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.38/1.55  % Solved by: fo/fo7.sh
% 1.38/1.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.38/1.55  % done 3349 iterations in 1.095s
% 1.38/1.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.38/1.55  % SZS output start Refutation
% 1.38/1.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.38/1.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.38/1.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.38/1.55  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.38/1.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.38/1.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.38/1.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.38/1.55  thf(sk_A_type, type, sk_A: $i).
% 1.38/1.55  thf(sk_B_type, type, sk_B: $i).
% 1.38/1.55  thf(sk_D_type, type, sk_D: $i).
% 1.38/1.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.38/1.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.38/1.55  thf(t149_zfmisc_1, conjecture,
% 1.38/1.55    (![A:$i,B:$i,C:$i,D:$i]:
% 1.38/1.55     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.38/1.55         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.38/1.55       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.38/1.55  thf(zf_stmt_0, negated_conjecture,
% 1.38/1.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.38/1.55        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.38/1.55            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.38/1.55          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.38/1.55    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.38/1.55  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 1.38/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.55  thf(commutativity_k3_xboole_0, axiom,
% 1.38/1.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.38/1.55  thf('1', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.38/1.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.38/1.55  thf(t17_xboole_1, axiom,
% 1.38/1.55    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.38/1.55  thf('2', plain,
% 1.38/1.55      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 1.38/1.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.38/1.55  thf('3', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.38/1.55      inference('sup+', [status(thm)], ['1', '2'])).
% 1.38/1.55  thf('4', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 1.38/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.55  thf(d7_xboole_0, axiom,
% 1.38/1.55    (![A:$i,B:$i]:
% 1.38/1.55     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.38/1.55       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.38/1.55  thf('5', plain,
% 1.38/1.55      (![X2 : $i, X3 : $i]:
% 1.38/1.55         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.38/1.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.38/1.55  thf('6', plain, (((k3_xboole_0 @ sk_C_2 @ sk_B) = (k1_xboole_0))),
% 1.38/1.55      inference('sup-', [status(thm)], ['4', '5'])).
% 1.38/1.55  thf('7', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.38/1.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.38/1.55  thf('8', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))),
% 1.38/1.55      inference('demod', [status(thm)], ['6', '7'])).
% 1.38/1.55  thf(t77_xboole_1, axiom,
% 1.38/1.55    (![A:$i,B:$i,C:$i]:
% 1.38/1.55     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 1.38/1.55          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 1.38/1.55  thf('9', plain,
% 1.38/1.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.38/1.55         ((r1_xboole_0 @ X18 @ X19)
% 1.38/1.55          | ~ (r1_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20))
% 1.38/1.55          | ~ (r1_tarski @ X18 @ X20))),
% 1.38/1.55      inference('cnf', [status(esa)], [t77_xboole_1])).
% 1.38/1.55  thf('10', plain,
% 1.38/1.55      (![X0 : $i]:
% 1.38/1.55         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 1.38/1.55          | ~ (r1_tarski @ X0 @ sk_C_2)
% 1.38/1.55          | (r1_xboole_0 @ X0 @ sk_B))),
% 1.38/1.55      inference('sup-', [status(thm)], ['8', '9'])).
% 1.38/1.55  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.38/1.55  thf('11', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 1.38/1.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.38/1.55  thf('12', plain,
% 1.38/1.55      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_C_2) | (r1_xboole_0 @ X0 @ sk_B))),
% 1.38/1.55      inference('demod', [status(thm)], ['10', '11'])).
% 1.38/1.55  thf('13', plain,
% 1.38/1.55      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C_2) @ sk_B)),
% 1.38/1.55      inference('sup-', [status(thm)], ['3', '12'])).
% 1.38/1.55  thf(t4_xboole_0, axiom,
% 1.38/1.55    (![A:$i,B:$i]:
% 1.38/1.55     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.38/1.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.38/1.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.38/1.55            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.38/1.55  thf('14', plain,
% 1.38/1.55      (![X9 : $i, X10 : $i]:
% 1.38/1.55         ((r1_xboole_0 @ X9 @ X10)
% 1.38/1.55          | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ (k3_xboole_0 @ X9 @ X10)))),
% 1.38/1.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.38/1.55  thf(l27_zfmisc_1, axiom,
% 1.38/1.55    (![A:$i,B:$i]:
% 1.38/1.55     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.38/1.55  thf('15', plain,
% 1.38/1.55      (![X30 : $i, X31 : $i]:
% 1.38/1.55         ((r1_xboole_0 @ (k1_tarski @ X30) @ X31) | (r2_hidden @ X30 @ X31))),
% 1.38/1.55      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.38/1.55  thf('16', plain,
% 1.38/1.55      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.38/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.55  thf('17', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.38/1.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.38/1.55  thf('18', plain,
% 1.38/1.55      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.38/1.55      inference('demod', [status(thm)], ['16', '17'])).
% 1.38/1.55  thf(t28_xboole_1, axiom,
% 1.38/1.55    (![A:$i,B:$i]:
% 1.38/1.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.38/1.55  thf('19', plain,
% 1.38/1.55      (![X15 : $i, X16 : $i]:
% 1.38/1.55         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 1.38/1.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.38/1.55  thf('20', plain,
% 1.38/1.55      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 1.38/1.55         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.38/1.55      inference('sup-', [status(thm)], ['18', '19'])).
% 1.38/1.55  thf('21', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.38/1.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.38/1.55  thf('22', plain,
% 1.38/1.55      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.38/1.55         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.38/1.55      inference('demod', [status(thm)], ['20', '21'])).
% 1.38/1.55  thf('23', plain,
% 1.38/1.55      (![X9 : $i, X11 : $i, X12 : $i]:
% 1.38/1.55         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 1.38/1.55          | ~ (r1_xboole_0 @ X9 @ X12))),
% 1.38/1.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.38/1.55  thf('24', plain,
% 1.38/1.55      (![X0 : $i]:
% 1.38/1.55         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.38/1.55          | ~ (r1_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.38/1.55      inference('sup-', [status(thm)], ['22', '23'])).
% 1.38/1.55  thf('25', plain,
% 1.38/1.55      (![X0 : $i]:
% 1.38/1.55         ((r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.38/1.55          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.38/1.55      inference('sup-', [status(thm)], ['15', '24'])).
% 1.38/1.55  thf('26', plain,
% 1.38/1.55      (((r1_xboole_0 @ sk_B @ sk_A)
% 1.38/1.55        | (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.38/1.55      inference('sup-', [status(thm)], ['14', '25'])).
% 1.38/1.55  thf('27', plain,
% 1.38/1.55      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 1.38/1.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.38/1.55  thf('28', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))),
% 1.38/1.55      inference('demod', [status(thm)], ['6', '7'])).
% 1.38/1.55  thf('29', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.38/1.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.38/1.55  thf('30', plain,
% 1.38/1.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.38/1.55         ((r1_xboole_0 @ X18 @ X19)
% 1.38/1.55          | ~ (r1_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20))
% 1.38/1.55          | ~ (r1_tarski @ X18 @ X20))),
% 1.38/1.55      inference('cnf', [status(esa)], [t77_xboole_1])).
% 1.38/1.55  thf('31', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.55         (~ (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.38/1.55          | ~ (r1_tarski @ X2 @ X1)
% 1.38/1.55          | (r1_xboole_0 @ X2 @ X0))),
% 1.38/1.55      inference('sup-', [status(thm)], ['29', '30'])).
% 1.38/1.55  thf('32', plain,
% 1.38/1.55      (![X0 : $i]:
% 1.38/1.55         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 1.38/1.55          | (r1_xboole_0 @ X0 @ sk_C_2)
% 1.38/1.55          | ~ (r1_tarski @ X0 @ sk_B))),
% 1.38/1.55      inference('sup-', [status(thm)], ['28', '31'])).
% 1.38/1.55  thf('33', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 1.38/1.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.38/1.55  thf('34', plain,
% 1.38/1.55      (![X0 : $i]: ((r1_xboole_0 @ X0 @ sk_C_2) | ~ (r1_tarski @ X0 @ sk_B))),
% 1.38/1.55      inference('demod', [status(thm)], ['32', '33'])).
% 1.38/1.55  thf('35', plain,
% 1.38/1.55      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_C_2)),
% 1.38/1.55      inference('sup-', [status(thm)], ['27', '34'])).
% 1.38/1.55  thf('36', plain,
% 1.38/1.55      (![X9 : $i, X10 : $i]:
% 1.38/1.55         ((r1_xboole_0 @ X9 @ X10)
% 1.38/1.55          | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ (k3_xboole_0 @ X9 @ X10)))),
% 1.38/1.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.38/1.55  thf('37', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.38/1.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.38/1.55  thf('38', plain,
% 1.38/1.55      (![X9 : $i, X11 : $i, X12 : $i]:
% 1.38/1.55         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 1.38/1.55          | ~ (r1_xboole_0 @ X9 @ X12))),
% 1.38/1.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.38/1.55  thf('39', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.38/1.55          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.38/1.55      inference('sup-', [status(thm)], ['37', '38'])).
% 1.38/1.55  thf('40', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i]:
% 1.38/1.55         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.38/1.55      inference('sup-', [status(thm)], ['36', '39'])).
% 1.38/1.55  thf('41', plain,
% 1.38/1.55      (![X0 : $i]: (r1_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ sk_B @ X0))),
% 1.38/1.55      inference('sup-', [status(thm)], ['35', '40'])).
% 1.38/1.55  thf('42', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 1.38/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.55  thf(t3_xboole_0, axiom,
% 1.38/1.55    (![A:$i,B:$i]:
% 1.38/1.55     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.38/1.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.38/1.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.38/1.55            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.38/1.55  thf('43', plain,
% 1.38/1.55      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.38/1.55         (~ (r2_hidden @ X7 @ X5)
% 1.38/1.55          | ~ (r2_hidden @ X7 @ X8)
% 1.38/1.55          | ~ (r1_xboole_0 @ X5 @ X8))),
% 1.38/1.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.38/1.55  thf('44', plain,
% 1.38/1.55      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 1.38/1.55      inference('sup-', [status(thm)], ['42', '43'])).
% 1.38/1.55  thf('45', plain,
% 1.38/1.55      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 1.38/1.55      inference('sup-', [status(thm)], ['41', '44'])).
% 1.38/1.55  thf('46', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.38/1.55      inference('sup-', [status(thm)], ['26', '45'])).
% 1.38/1.55  thf(t78_xboole_1, axiom,
% 1.38/1.55    (![A:$i,B:$i,C:$i]:
% 1.38/1.55     ( ( r1_xboole_0 @ A @ B ) =>
% 1.38/1.55       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.38/1.55         ( k3_xboole_0 @ A @ C ) ) ))).
% 1.38/1.55  thf('47', plain,
% 1.38/1.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.38/1.55         (~ (r1_xboole_0 @ X21 @ X22)
% 1.38/1.55          | ((k3_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 1.38/1.55              = (k3_xboole_0 @ X21 @ X23)))),
% 1.38/1.55      inference('cnf', [status(esa)], [t78_xboole_1])).
% 1.38/1.55  thf('48', plain,
% 1.38/1.55      (![X0 : $i]:
% 1.38/1.55         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 1.38/1.55           = (k3_xboole_0 @ sk_B @ X0))),
% 1.38/1.55      inference('sup-', [status(thm)], ['46', '47'])).
% 1.38/1.55  thf('49', plain,
% 1.38/1.55      (![X9 : $i, X10 : $i]:
% 1.38/1.55         ((r1_xboole_0 @ X9 @ X10)
% 1.38/1.55          | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ (k3_xboole_0 @ X9 @ X10)))),
% 1.38/1.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.38/1.55  thf('50', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.38/1.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.38/1.55  thf('51', plain,
% 1.38/1.55      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 1.38/1.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.38/1.55  thf('52', plain,
% 1.38/1.55      (![X15 : $i, X16 : $i]:
% 1.38/1.55         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 1.38/1.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.38/1.55  thf('53', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i]:
% 1.38/1.55         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.38/1.55           = (k3_xboole_0 @ X0 @ X1))),
% 1.38/1.55      inference('sup-', [status(thm)], ['51', '52'])).
% 1.38/1.55  thf('54', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.38/1.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.38/1.55  thf('55', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i]:
% 1.38/1.55         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.38/1.55           = (k3_xboole_0 @ X0 @ X1))),
% 1.38/1.55      inference('demod', [status(thm)], ['53', '54'])).
% 1.38/1.55  thf('56', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.38/1.55          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.38/1.55      inference('sup-', [status(thm)], ['37', '38'])).
% 1.38/1.55  thf('57', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.38/1.55          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.38/1.55      inference('sup-', [status(thm)], ['55', '56'])).
% 1.38/1.55  thf('58', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.38/1.55          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 1.38/1.55      inference('sup-', [status(thm)], ['50', '57'])).
% 1.38/1.55  thf('59', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i]:
% 1.38/1.55         ((r1_xboole_0 @ X1 @ X0)
% 1.38/1.55          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 1.38/1.55      inference('sup-', [status(thm)], ['49', '58'])).
% 1.38/1.55  thf('60', plain,
% 1.38/1.55      (![X0 : $i]:
% 1.38/1.55         (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)
% 1.38/1.55          | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 1.38/1.55      inference('sup-', [status(thm)], ['48', '59'])).
% 1.38/1.55  thf('61', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 1.38/1.55      inference('sup-', [status(thm)], ['13', '60'])).
% 1.38/1.55  thf('62', plain, ($false), inference('demod', [status(thm)], ['0', '61'])).
% 1.38/1.55  
% 1.38/1.55  % SZS output end Refutation
% 1.38/1.55  
% 1.38/1.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
