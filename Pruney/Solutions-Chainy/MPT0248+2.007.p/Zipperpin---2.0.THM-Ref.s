%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yEZlY9wbxm

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:18 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 223 expanded)
%              Number of leaves         :   26 (  67 expanded)
%              Depth                    :   18
%              Number of atoms          :  681 (2804 expanded)
%              Number of equality atoms :  123 ( 617 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('7',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X29
        = ( k2_tarski @ X27 @ X28 ) )
      | ( X29
        = ( k1_tarski @ X28 ) )
      | ( X29
        = ( k1_tarski @ X27 ) )
      | ( X29 = k1_xboole_0 )
      | ~ ( r1_tarski @ X29 @ ( k2_tarski @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_C
      = ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf('18',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_C
     != ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('23',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('27',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( sk_B
     != ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('35',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['22','24','36'])).

thf('38',plain,(
    sk_C
 != ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['21','37'])).

thf('39',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['17','38'])).

thf('40',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('41',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('43',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('45',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('48',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r1_xboole_0 @ X13 @ X16 )
      | ~ ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('54',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('56',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('59',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['41','60'])).

thf('62',plain,(
    sk_C
 != ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['21','37'])).

thf('63',plain,
    ( ( sk_C != sk_C )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['29'])).

thf('66',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['64','65'])).

thf('67',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['40','66'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yEZlY9wbxm
% 0.13/0.37  % Computer   : n013.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 09:27:40 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.36/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.57  % Solved by: fo/fo7.sh
% 0.36/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.57  % done 250 iterations in 0.091s
% 0.36/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.57  % SZS output start Refutation
% 0.36/0.57  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(commutativity_k2_tarski, axiom,
% 0.36/0.57    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.36/0.57  thf('0', plain,
% 0.36/0.57      (![X19 : $i, X20 : $i]:
% 0.36/0.57         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 0.36/0.57      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.36/0.57  thf(l51_zfmisc_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.57  thf('1', plain,
% 0.36/0.57      (![X31 : $i, X32 : $i]:
% 0.36/0.57         ((k3_tarski @ (k2_tarski @ X31 @ X32)) = (k2_xboole_0 @ X31 @ X32))),
% 0.36/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.36/0.57  thf('2', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('sup+', [status(thm)], ['0', '1'])).
% 0.36/0.57  thf('3', plain,
% 0.36/0.57      (![X31 : $i, X32 : $i]:
% 0.36/0.57         ((k3_tarski @ (k2_tarski @ X31 @ X32)) = (k2_xboole_0 @ X31 @ X32))),
% 0.36/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.36/0.57  thf('4', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.57  thf(t7_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.57  thf('5', plain,
% 0.36/0.57      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.36/0.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.36/0.57  thf('6', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.36/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.36/0.57  thf(t43_zfmisc_1, conjecture,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.36/0.57          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.36/0.57          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.36/0.57          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.36/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.57        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.36/0.57             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.36/0.57             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.36/0.57             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.36/0.57    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.36/0.57  thf('7', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t69_enumset1, axiom,
% 0.36/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.57  thf('8', plain, (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.36/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.57  thf(l45_zfmisc_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.36/0.57       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.36/0.57            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.36/0.57  thf('9', plain,
% 0.36/0.57      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.36/0.57         (((X29) = (k2_tarski @ X27 @ X28))
% 0.36/0.57          | ((X29) = (k1_tarski @ X28))
% 0.36/0.57          | ((X29) = (k1_tarski @ X27))
% 0.36/0.57          | ((X29) = (k1_xboole_0))
% 0.36/0.57          | ~ (r1_tarski @ X29 @ (k2_tarski @ X27 @ X28)))),
% 0.36/0.57      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.36/0.57  thf('10', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.36/0.57          | ((X1) = (k1_xboole_0))
% 0.36/0.57          | ((X1) = (k1_tarski @ X0))
% 0.36/0.57          | ((X1) = (k1_tarski @ X0))
% 0.36/0.57          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.57  thf('11', plain,
% 0.36/0.57      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.36/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.57  thf('12', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.36/0.57          | ((X1) = (k1_xboole_0))
% 0.36/0.57          | ((X1) = (k1_tarski @ X0))
% 0.36/0.57          | ((X1) = (k1_tarski @ X0))
% 0.36/0.57          | ((X1) = (k1_tarski @ X0)))),
% 0.36/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.57  thf('13', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (((X1) = (k1_tarski @ X0))
% 0.36/0.57          | ((X1) = (k1_xboole_0))
% 0.36/0.57          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.36/0.57      inference('simplify', [status(thm)], ['12'])).
% 0.36/0.57  thf('14', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.36/0.57          | ((X0) = (k1_xboole_0))
% 0.36/0.57          | ((X0) = (k1_tarski @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['7', '13'])).
% 0.36/0.57  thf('15', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('16', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.36/0.57          | ((X0) = (k1_xboole_0))
% 0.36/0.57          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.36/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.36/0.57  thf('17', plain,
% 0.36/0.57      ((((sk_C) = (k2_xboole_0 @ sk_B @ sk_C)) | ((sk_C) = (k1_xboole_0)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['6', '16'])).
% 0.36/0.57  thf('18', plain,
% 0.36/0.57      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('19', plain,
% 0.36/0.57      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.36/0.57      inference('split', [status(esa)], ['18'])).
% 0.36/0.57  thf('20', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('21', plain,
% 0.36/0.57      ((((sk_C) != (k2_xboole_0 @ sk_B @ sk_C)))
% 0.36/0.57         <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.36/0.57      inference('demod', [status(thm)], ['19', '20'])).
% 0.36/0.57  thf('22', plain,
% 0.36/0.57      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.36/0.57      inference('split', [status(esa)], ['18'])).
% 0.36/0.57  thf('23', plain,
% 0.36/0.57      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('24', plain,
% 0.36/0.57      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.36/0.57      inference('split', [status(esa)], ['23'])).
% 0.36/0.57  thf('25', plain,
% 0.36/0.57      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.36/0.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.36/0.57  thf('26', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.36/0.57          | ((X0) = (k1_xboole_0))
% 0.36/0.57          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.36/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.36/0.57  thf('27', plain,
% 0.36/0.57      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C)) | ((sk_B) = (k1_xboole_0)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.57  thf('28', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('29', plain,
% 0.36/0.57      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('30', plain,
% 0.36/0.57      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.36/0.57      inference('split', [status(esa)], ['29'])).
% 0.36/0.57  thf('31', plain,
% 0.36/0.57      ((((sk_B) != (k2_xboole_0 @ sk_B @ sk_C)))
% 0.36/0.57         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['28', '30'])).
% 0.36/0.57  thf('32', plain,
% 0.36/0.57      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.36/0.57         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['27', '31'])).
% 0.36/0.57  thf('33', plain,
% 0.36/0.57      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.36/0.57      inference('simplify', [status(thm)], ['32'])).
% 0.36/0.57  thf('34', plain,
% 0.36/0.57      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.36/0.57      inference('split', [status(esa)], ['18'])).
% 0.36/0.57  thf('35', plain,
% 0.36/0.57      ((((sk_B) != (sk_B)))
% 0.36/0.57         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.57  thf('36', plain,
% 0.36/0.57      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.36/0.57      inference('simplify', [status(thm)], ['35'])).
% 0.36/0.57  thf('37', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.36/0.57      inference('sat_resolution*', [status(thm)], ['22', '24', '36'])).
% 0.36/0.57  thf('38', plain, (((sk_C) != (k2_xboole_0 @ sk_B @ sk_C))),
% 0.36/0.57      inference('simpl_trail', [status(thm)], ['21', '37'])).
% 0.36/0.57  thf('39', plain, (((sk_C) = (k1_xboole_0))),
% 0.36/0.57      inference('simplify_reflect-', [status(thm)], ['17', '38'])).
% 0.36/0.57  thf('40', plain,
% 0.36/0.57      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.36/0.57      inference('split', [status(esa)], ['29'])).
% 0.36/0.57  thf('41', plain,
% 0.36/0.57      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.36/0.57      inference('simplify', [status(thm)], ['32'])).
% 0.36/0.57  thf('42', plain,
% 0.36/0.57      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.36/0.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.36/0.57  thf(t28_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.57  thf('43', plain,
% 0.36/0.57      (![X10 : $i, X11 : $i]:
% 0.36/0.57         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.36/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.57  thf('44', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.36/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.36/0.57  thf(d7_xboole_0, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.36/0.57       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.57  thf('45', plain,
% 0.36/0.57      (![X0 : $i, X2 : $i]:
% 0.36/0.57         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.36/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.36/0.57  thf('46', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (((X0) != (k1_xboole_0))
% 0.36/0.57          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['44', '45'])).
% 0.36/0.57  thf('47', plain,
% 0.36/0.57      (![X1 : $i]:
% 0.36/0.57         (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))),
% 0.36/0.57      inference('simplify', [status(thm)], ['46'])).
% 0.36/0.57  thf(t70_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.36/0.57            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.36/0.57       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.36/0.57            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.36/0.57  thf('48', plain,
% 0.36/0.57      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.36/0.57         ((r1_xboole_0 @ X13 @ X16)
% 0.36/0.57          | ~ (r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X16)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.36/0.57  thf('49', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.36/0.57      inference('sup-', [status(thm)], ['47', '48'])).
% 0.36/0.57  thf('50', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.36/0.57  thf('51', plain,
% 0.36/0.57      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.57  thf(t100_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.57  thf('52', plain,
% 0.36/0.57      (![X6 : $i, X7 : $i]:
% 0.36/0.57         ((k4_xboole_0 @ X6 @ X7)
% 0.36/0.57           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.57  thf('53', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.36/0.57           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.36/0.57      inference('sup+', [status(thm)], ['51', '52'])).
% 0.36/0.57  thf(t5_boole, axiom,
% 0.36/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.57  thf('54', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.36/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.36/0.57  thf('55', plain,
% 0.36/0.57      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.57      inference('demod', [status(thm)], ['53', '54'])).
% 0.36/0.57  thf(l32_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.58  thf('56', plain,
% 0.36/0.58      (![X3 : $i, X4 : $i]:
% 0.36/0.58         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.36/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.58  thf('57', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['55', '56'])).
% 0.36/0.58  thf('58', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.36/0.58      inference('simplify', [status(thm)], ['57'])).
% 0.36/0.58  thf(t12_xboole_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.36/0.58  thf('59', plain,
% 0.36/0.58      (![X8 : $i, X9 : $i]:
% 0.36/0.58         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.36/0.58      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.58  thf('60', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['58', '59'])).
% 0.36/0.58  thf('61', plain,
% 0.36/0.58      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.36/0.58         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.36/0.58      inference('sup+', [status(thm)], ['41', '60'])).
% 0.36/0.58  thf('62', plain, (((sk_C) != (k2_xboole_0 @ sk_B @ sk_C))),
% 0.36/0.58      inference('simpl_trail', [status(thm)], ['21', '37'])).
% 0.36/0.58  thf('63', plain,
% 0.36/0.58      ((((sk_C) != (sk_C))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.58  thf('64', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.36/0.58      inference('simplify', [status(thm)], ['63'])).
% 0.36/0.58  thf('65', plain,
% 0.36/0.58      (~ (((sk_C) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.36/0.58      inference('split', [status(esa)], ['29'])).
% 0.36/0.58  thf('66', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.36/0.58      inference('sat_resolution*', [status(thm)], ['64', '65'])).
% 0.36/0.58  thf('67', plain, (((sk_C) != (k1_xboole_0))),
% 0.36/0.58      inference('simpl_trail', [status(thm)], ['40', '66'])).
% 0.36/0.58  thf('68', plain, ($false),
% 0.36/0.58      inference('simplify_reflect-', [status(thm)], ['39', '67'])).
% 0.36/0.58  
% 0.36/0.58  % SZS output end Refutation
% 0.36/0.58  
% 0.36/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
