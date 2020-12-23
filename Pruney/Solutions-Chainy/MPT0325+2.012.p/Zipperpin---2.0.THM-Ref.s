%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NAuA3spcOg

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:41 EST 2020

% Result     : Theorem 3.81s
% Output     : Refutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 182 expanded)
%              Number of leaves         :   23 (  62 expanded)
%              Depth                    :   24
%              Number of atoms          :  811 (1500 expanded)
%              Number of equality atoms :   88 ( 155 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t138_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
       => ( ( ( k2_zfmisc_1 @ A @ B )
            = k1_xboole_0 )
          | ( ( r1_tarski @ A @ C )
            & ( r1_tarski @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t138_zfmisc_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X19: $i] :
      ( ( k2_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ X28 @ ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('13',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X26 @ X27 ) @ X27 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('18',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X43 @ X45 ) @ ( k3_xboole_0 @ X44 @ X46 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X43 @ X44 ) @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('19',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ( ( k3_xboole_0 @ X5 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X0 ) @ ( k2_zfmisc_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('22',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_zfmisc_1 @ X31 @ X32 )
        = k1_xboole_0 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('23',plain,(
    ! [X31: $i] :
      ( ( k2_zfmisc_1 @ X31 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X0 ) @ ( k2_zfmisc_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X0 ) @ ( k2_zfmisc_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X23 @ X24 )
      | ~ ( r1_xboole_0 @ X24 @ X25 )
      | ( r1_xboole_0 @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ sk_D ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X43 @ X45 ) @ ( k3_xboole_0 @ X44 @ X46 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X43 @ X44 ) @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ sk_A ) @ ( k3_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_D ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_D ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','36'])).

thf('38',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['9','37'])).

thf('39',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X31 @ X30 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( ( k4_xboole_0 @ X13 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X3 @ X2 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_zfmisc_1 @ X31 @ X32 )
        = k1_xboole_0 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('53',plain,(
    ! [X32: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X32 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X3 @ X2 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X3 @ X2 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ sk_C_1 ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X1 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X1 @ sk_C_1 ) ) @ ( k3_xboole_0 @ X0 @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ X0 @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','62'])).

thf('64',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['47','63'])).

thf('65',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X31 @ X30 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('66',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( ( k4_xboole_0 @ X13 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('69',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r1_tarski @ sk_A @ sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['45'])).

thf('72',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X31: $i] :
      ( ( k2_zfmisc_1 @ X31 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('76',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D )
    | ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['45'])).

thf('79',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['46','79'])).

thf('81',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['44','80'])).

thf('82',plain,(
    ! [X32: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X32 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('83',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','81','82'])).

thf('84',plain,(
    $false ),
    inference(simplify,[status(thm)],['83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NAuA3spcOg
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:02:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.81/4.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.81/4.01  % Solved by: fo/fo7.sh
% 3.81/4.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.81/4.01  % done 10413 iterations in 3.556s
% 3.81/4.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.81/4.01  % SZS output start Refutation
% 3.81/4.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.81/4.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.81/4.01  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.81/4.01  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.81/4.01  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.81/4.01  thf(sk_D_type, type, sk_D: $i).
% 3.81/4.01  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.81/4.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.81/4.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.81/4.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.81/4.01  thf(sk_A_type, type, sk_A: $i).
% 3.81/4.01  thf(t138_zfmisc_1, conjecture,
% 3.81/4.01    (![A:$i,B:$i,C:$i,D:$i]:
% 3.81/4.01     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 3.81/4.01       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 3.81/4.01         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 3.81/4.01  thf(zf_stmt_0, negated_conjecture,
% 3.81/4.01    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.81/4.01        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 3.81/4.01          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 3.81/4.01            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 3.81/4.01    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 3.81/4.01  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 3.81/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.01  thf(t1_boole, axiom,
% 3.81/4.01    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.81/4.01  thf('1', plain, (![X19 : $i]: ((k2_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 3.81/4.01      inference('cnf', [status(esa)], [t1_boole])).
% 3.81/4.01  thf(t7_xboole_1, axiom,
% 3.81/4.01    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 3.81/4.01  thf('2', plain,
% 3.81/4.01      (![X28 : $i, X29 : $i]: (r1_tarski @ X28 @ (k2_xboole_0 @ X28 @ X29))),
% 3.81/4.01      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.81/4.01  thf('3', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 3.81/4.01      inference('sup+', [status(thm)], ['1', '2'])).
% 3.81/4.01  thf(t106_xboole_1, axiom,
% 3.81/4.01    (![A:$i,B:$i,C:$i]:
% 3.81/4.01     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 3.81/4.01       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 3.81/4.01  thf('4', plain,
% 3.81/4.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.81/4.01         ((r1_tarski @ X16 @ X17)
% 3.81/4.01          | ~ (r1_tarski @ X16 @ (k4_xboole_0 @ X17 @ X18)))),
% 3.81/4.01      inference('cnf', [status(esa)], [t106_xboole_1])).
% 3.81/4.01  thf('5', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 3.81/4.01      inference('sup-', [status(thm)], ['3', '4'])).
% 3.81/4.01  thf(t28_xboole_1, axiom,
% 3.81/4.01    (![A:$i,B:$i]:
% 3.81/4.01     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.81/4.01  thf('6', plain,
% 3.81/4.01      (![X20 : $i, X21 : $i]:
% 3.81/4.01         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 3.81/4.01      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.81/4.01  thf('7', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i]:
% 3.81/4.01         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 3.81/4.01           = (k4_xboole_0 @ X0 @ X1))),
% 3.81/4.01      inference('sup-', [status(thm)], ['5', '6'])).
% 3.81/4.01  thf(commutativity_k3_xboole_0, axiom,
% 3.81/4.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.81/4.01  thf('8', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.81/4.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.81/4.01  thf('9', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i]:
% 3.81/4.01         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 3.81/4.01           = (k4_xboole_0 @ X0 @ X1))),
% 3.81/4.01      inference('demod', [status(thm)], ['7', '8'])).
% 3.81/4.01  thf('10', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 3.81/4.01      inference('sup+', [status(thm)], ['1', '2'])).
% 3.81/4.01  thf('11', plain,
% 3.81/4.01      (![X20 : $i, X21 : $i]:
% 3.81/4.01         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 3.81/4.01      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.81/4.01  thf('12', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 3.81/4.01      inference('sup-', [status(thm)], ['10', '11'])).
% 3.81/4.01  thf(t79_xboole_1, axiom,
% 3.81/4.01    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 3.81/4.01  thf('13', plain,
% 3.81/4.01      (![X26 : $i, X27 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X26 @ X27) @ X27)),
% 3.81/4.01      inference('cnf', [status(esa)], [t79_xboole_1])).
% 3.81/4.01  thf(d7_xboole_0, axiom,
% 3.81/4.01    (![A:$i,B:$i]:
% 3.81/4.01     ( ( r1_xboole_0 @ A @ B ) <=>
% 3.81/4.01       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 3.81/4.01  thf('14', plain,
% 3.81/4.01      (![X5 : $i, X6 : $i]:
% 3.81/4.01         (((k3_xboole_0 @ X5 @ X6) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 3.81/4.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.81/4.01  thf('15', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i]:
% 3.81/4.01         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 3.81/4.01      inference('sup-', [status(thm)], ['13', '14'])).
% 3.81/4.01  thf('16', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.81/4.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.81/4.01  thf('17', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i]:
% 3.81/4.01         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 3.81/4.01      inference('demod', [status(thm)], ['15', '16'])).
% 3.81/4.01  thf(t123_zfmisc_1, axiom,
% 3.81/4.01    (![A:$i,B:$i,C:$i,D:$i]:
% 3.81/4.01     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 3.81/4.01       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 3.81/4.01  thf('18', plain,
% 3.81/4.01      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 3.81/4.01         ((k2_zfmisc_1 @ (k3_xboole_0 @ X43 @ X45) @ (k3_xboole_0 @ X44 @ X46))
% 3.81/4.01           = (k3_xboole_0 @ (k2_zfmisc_1 @ X43 @ X44) @ 
% 3.81/4.01              (k2_zfmisc_1 @ X45 @ X46)))),
% 3.81/4.01      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 3.81/4.01  thf('19', plain,
% 3.81/4.01      (![X5 : $i, X7 : $i]:
% 3.81/4.01         ((r1_xboole_0 @ X5 @ X7) | ((k3_xboole_0 @ X5 @ X7) != (k1_xboole_0)))),
% 3.81/4.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.81/4.01  thf('20', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.81/4.01         (((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 3.81/4.01            != (k1_xboole_0))
% 3.81/4.01          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 3.81/4.01      inference('sup-', [status(thm)], ['18', '19'])).
% 3.81/4.01  thf('21', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.81/4.01         (((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ k1_xboole_0)
% 3.81/4.01            != (k1_xboole_0))
% 3.81/4.01          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X0) @ 
% 3.81/4.01             (k2_zfmisc_1 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 3.81/4.01      inference('sup-', [status(thm)], ['17', '20'])).
% 3.81/4.01  thf(t113_zfmisc_1, axiom,
% 3.81/4.01    (![A:$i,B:$i]:
% 3.81/4.01     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.81/4.01       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.81/4.01  thf('22', plain,
% 3.81/4.01      (![X31 : $i, X32 : $i]:
% 3.81/4.01         (((k2_zfmisc_1 @ X31 @ X32) = (k1_xboole_0))
% 3.81/4.01          | ((X32) != (k1_xboole_0)))),
% 3.81/4.01      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.81/4.01  thf('23', plain,
% 3.81/4.01      (![X31 : $i]: ((k2_zfmisc_1 @ X31 @ k1_xboole_0) = (k1_xboole_0))),
% 3.81/4.01      inference('simplify', [status(thm)], ['22'])).
% 3.81/4.01  thf('24', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.81/4.01         (((k1_xboole_0) != (k1_xboole_0))
% 3.81/4.01          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X0) @ 
% 3.81/4.01             (k2_zfmisc_1 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 3.81/4.01      inference('demod', [status(thm)], ['21', '23'])).
% 3.81/4.01  thf('25', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.81/4.01         (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X0) @ 
% 3.81/4.01          (k2_zfmisc_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.81/4.01      inference('simplify', [status(thm)], ['24'])).
% 3.81/4.01  thf('26', plain,
% 3.81/4.01      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.01        (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 3.81/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.01  thf(t63_xboole_1, axiom,
% 3.81/4.01    (![A:$i,B:$i,C:$i]:
% 3.81/4.01     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 3.81/4.01       ( r1_xboole_0 @ A @ C ) ))).
% 3.81/4.01  thf('27', plain,
% 3.81/4.01      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.81/4.01         (~ (r1_tarski @ X23 @ X24)
% 3.81/4.01          | ~ (r1_xboole_0 @ X24 @ X25)
% 3.81/4.01          | (r1_xboole_0 @ X23 @ X25))),
% 3.81/4.01      inference('cnf', [status(esa)], [t63_xboole_1])).
% 3.81/4.01  thf('28', plain,
% 3.81/4.01      (![X0 : $i]:
% 3.81/4.01         ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ X0)
% 3.81/4.01          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ X0))),
% 3.81/4.01      inference('sup-', [status(thm)], ['26', '27'])).
% 3.81/4.01  thf('29', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i]:
% 3.81/4.01         (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.01          (k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ sk_D)))),
% 3.81/4.01      inference('sup-', [status(thm)], ['25', '28'])).
% 3.81/4.01  thf('30', plain,
% 3.81/4.01      (![X5 : $i, X6 : $i]:
% 3.81/4.01         (((k3_xboole_0 @ X5 @ X6) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 3.81/4.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.81/4.01  thf('31', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i]:
% 3.81/4.01         ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.01           (k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ sk_D))) = (k1_xboole_0))),
% 3.81/4.01      inference('sup-', [status(thm)], ['29', '30'])).
% 3.81/4.01  thf('32', plain,
% 3.81/4.01      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 3.81/4.01         ((k2_zfmisc_1 @ (k3_xboole_0 @ X43 @ X45) @ (k3_xboole_0 @ X44 @ X46))
% 3.81/4.01           = (k3_xboole_0 @ (k2_zfmisc_1 @ X43 @ X44) @ 
% 3.81/4.01              (k2_zfmisc_1 @ X45 @ X46)))),
% 3.81/4.01      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 3.81/4.01  thf('33', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.81/4.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.81/4.01  thf('34', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.81/4.01         ((k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X3 @ X1))
% 3.81/4.01           = (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 3.81/4.01      inference('sup+', [status(thm)], ['32', '33'])).
% 3.81/4.01  thf('35', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.81/4.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.81/4.01  thf('36', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i]:
% 3.81/4.01         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ sk_A) @ 
% 3.81/4.01           (k3_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_D))) = (k1_xboole_0))),
% 3.81/4.01      inference('demod', [status(thm)], ['31', '34', '35'])).
% 3.81/4.01  thf('37', plain,
% 3.81/4.01      (![X0 : $i]:
% 3.81/4.01         ((k2_zfmisc_1 @ sk_A @ 
% 3.81/4.01           (k3_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_D))) = (k1_xboole_0))),
% 3.81/4.01      inference('sup+', [status(thm)], ['12', '36'])).
% 3.81/4.01  thf('38', plain,
% 3.81/4.01      (((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_D)) = (k1_xboole_0))),
% 3.81/4.01      inference('sup+', [status(thm)], ['9', '37'])).
% 3.81/4.01  thf('39', plain,
% 3.81/4.01      (![X30 : $i, X31 : $i]:
% 3.81/4.01         (((X30) = (k1_xboole_0))
% 3.81/4.01          | ((X31) = (k1_xboole_0))
% 3.81/4.01          | ((k2_zfmisc_1 @ X31 @ X30) != (k1_xboole_0)))),
% 3.81/4.01      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.81/4.01  thf('40', plain,
% 3.81/4.01      ((((k1_xboole_0) != (k1_xboole_0))
% 3.81/4.01        | ((sk_A) = (k1_xboole_0))
% 3.81/4.01        | ((k4_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0)))),
% 3.81/4.01      inference('sup-', [status(thm)], ['38', '39'])).
% 3.81/4.01  thf('41', plain,
% 3.81/4.01      ((((k4_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))
% 3.81/4.01        | ((sk_A) = (k1_xboole_0)))),
% 3.81/4.01      inference('simplify', [status(thm)], ['40'])).
% 3.81/4.01  thf(l32_xboole_1, axiom,
% 3.81/4.01    (![A:$i,B:$i]:
% 3.81/4.01     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.81/4.01  thf('42', plain,
% 3.81/4.01      (![X13 : $i, X14 : $i]:
% 3.81/4.01         ((r1_tarski @ X13 @ X14)
% 3.81/4.01          | ((k4_xboole_0 @ X13 @ X14) != (k1_xboole_0)))),
% 3.81/4.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.81/4.01  thf('43', plain,
% 3.81/4.01      ((((k1_xboole_0) != (k1_xboole_0))
% 3.81/4.01        | ((sk_A) = (k1_xboole_0))
% 3.81/4.01        | (r1_tarski @ sk_B_1 @ sk_D))),
% 3.81/4.01      inference('sup-', [status(thm)], ['41', '42'])).
% 3.81/4.01  thf('44', plain, (((r1_tarski @ sk_B_1 @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 3.81/4.01      inference('simplify', [status(thm)], ['43'])).
% 3.81/4.01  thf('45', plain,
% 3.81/4.01      ((~ (r1_tarski @ sk_A @ sk_C_1) | ~ (r1_tarski @ sk_B_1 @ sk_D))),
% 3.81/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.01  thf('46', plain,
% 3.81/4.01      ((~ (r1_tarski @ sk_B_1 @ sk_D)) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 3.81/4.01      inference('split', [status(esa)], ['45'])).
% 3.81/4.01  thf('47', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 3.81/4.01      inference('sup-', [status(thm)], ['10', '11'])).
% 3.81/4.01  thf('48', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i]:
% 3.81/4.01         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 3.81/4.01           = (k4_xboole_0 @ X0 @ X1))),
% 3.81/4.01      inference('demod', [status(thm)], ['7', '8'])).
% 3.81/4.01  thf('49', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i]:
% 3.81/4.01         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 3.81/4.01      inference('demod', [status(thm)], ['15', '16'])).
% 3.81/4.01  thf('50', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.81/4.01         (((k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 3.81/4.01            != (k1_xboole_0))
% 3.81/4.01          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 3.81/4.01      inference('sup-', [status(thm)], ['18', '19'])).
% 3.81/4.01  thf('51', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.81/4.01         (((k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 3.81/4.01            != (k1_xboole_0))
% 3.81/4.01          | (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ 
% 3.81/4.01             (k2_zfmisc_1 @ (k4_xboole_0 @ X3 @ X2) @ X0)))),
% 3.81/4.01      inference('sup-', [status(thm)], ['49', '50'])).
% 3.81/4.01  thf('52', plain,
% 3.81/4.01      (![X31 : $i, X32 : $i]:
% 3.81/4.01         (((k2_zfmisc_1 @ X31 @ X32) = (k1_xboole_0))
% 3.81/4.01          | ((X31) != (k1_xboole_0)))),
% 3.81/4.01      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.81/4.01  thf('53', plain,
% 3.81/4.01      (![X32 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X32) = (k1_xboole_0))),
% 3.81/4.01      inference('simplify', [status(thm)], ['52'])).
% 3.81/4.01  thf('54', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.81/4.01         (((k1_xboole_0) != (k1_xboole_0))
% 3.81/4.01          | (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ 
% 3.81/4.01             (k2_zfmisc_1 @ (k4_xboole_0 @ X3 @ X2) @ X0)))),
% 3.81/4.01      inference('demod', [status(thm)], ['51', '53'])).
% 3.81/4.01  thf('55', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.81/4.01         (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ 
% 3.81/4.01          (k2_zfmisc_1 @ (k4_xboole_0 @ X3 @ X2) @ X0))),
% 3.81/4.01      inference('simplify', [status(thm)], ['54'])).
% 3.81/4.01  thf('56', plain,
% 3.81/4.01      (![X0 : $i]:
% 3.81/4.01         ((r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ X0)
% 3.81/4.01          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D) @ X0))),
% 3.81/4.01      inference('sup-', [status(thm)], ['26', '27'])).
% 3.81/4.01  thf('57', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i]:
% 3.81/4.01         (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.01          (k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ sk_C_1) @ X0))),
% 3.81/4.01      inference('sup-', [status(thm)], ['55', '56'])).
% 3.81/4.01  thf('58', plain,
% 3.81/4.01      (![X5 : $i, X6 : $i]:
% 3.81/4.01         (((k3_xboole_0 @ X5 @ X6) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 3.81/4.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.81/4.01  thf('59', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i]:
% 3.81/4.01         ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 3.81/4.01           (k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ sk_C_1) @ X0)) = (k1_xboole_0))),
% 3.81/4.01      inference('sup-', [status(thm)], ['57', '58'])).
% 3.81/4.01  thf('60', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.81/4.01         ((k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X3 @ X1))
% 3.81/4.01           = (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 3.81/4.01      inference('sup+', [status(thm)], ['32', '33'])).
% 3.81/4.01  thf('61', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.81/4.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.81/4.01  thf('62', plain,
% 3.81/4.01      (![X0 : $i, X1 : $i]:
% 3.81/4.01         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X1 @ sk_C_1)) @ 
% 3.81/4.01           (k3_xboole_0 @ X0 @ sk_B_1)) = (k1_xboole_0))),
% 3.81/4.01      inference('demod', [status(thm)], ['59', '60', '61'])).
% 3.81/4.01  thf('63', plain,
% 3.81/4.01      (![X0 : $i]:
% 3.81/4.01         ((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 3.81/4.01           (k3_xboole_0 @ X0 @ sk_B_1)) = (k1_xboole_0))),
% 3.81/4.01      inference('sup+', [status(thm)], ['48', '62'])).
% 3.81/4.01  thf('64', plain,
% 3.81/4.01      (((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_B_1) = (k1_xboole_0))),
% 3.81/4.01      inference('sup+', [status(thm)], ['47', '63'])).
% 3.81/4.01  thf('65', plain,
% 3.81/4.01      (![X30 : $i, X31 : $i]:
% 3.81/4.01         (((X30) = (k1_xboole_0))
% 3.81/4.01          | ((X31) = (k1_xboole_0))
% 3.81/4.01          | ((k2_zfmisc_1 @ X31 @ X30) != (k1_xboole_0)))),
% 3.81/4.01      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.81/4.01  thf('66', plain,
% 3.81/4.01      ((((k1_xboole_0) != (k1_xboole_0))
% 3.81/4.01        | ((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))
% 3.81/4.01        | ((sk_B_1) = (k1_xboole_0)))),
% 3.81/4.01      inference('sup-', [status(thm)], ['64', '65'])).
% 3.81/4.01  thf('67', plain,
% 3.81/4.01      ((((sk_B_1) = (k1_xboole_0))
% 3.81/4.01        | ((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0)))),
% 3.81/4.01      inference('simplify', [status(thm)], ['66'])).
% 3.81/4.01  thf('68', plain,
% 3.81/4.01      (![X13 : $i, X14 : $i]:
% 3.81/4.01         ((r1_tarski @ X13 @ X14)
% 3.81/4.01          | ((k4_xboole_0 @ X13 @ X14) != (k1_xboole_0)))),
% 3.81/4.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.81/4.01  thf('69', plain,
% 3.81/4.01      ((((k1_xboole_0) != (k1_xboole_0))
% 3.81/4.01        | ((sk_B_1) = (k1_xboole_0))
% 3.81/4.01        | (r1_tarski @ sk_A @ sk_C_1))),
% 3.81/4.01      inference('sup-', [status(thm)], ['67', '68'])).
% 3.81/4.01  thf('70', plain,
% 3.81/4.01      (((r1_tarski @ sk_A @ sk_C_1) | ((sk_B_1) = (k1_xboole_0)))),
% 3.81/4.01      inference('simplify', [status(thm)], ['69'])).
% 3.81/4.01  thf('71', plain,
% 3.81/4.01      ((~ (r1_tarski @ sk_A @ sk_C_1)) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 3.81/4.01      inference('split', [status(esa)], ['45'])).
% 3.81/4.01  thf('72', plain,
% 3.81/4.01      ((((sk_B_1) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 3.81/4.01      inference('sup-', [status(thm)], ['70', '71'])).
% 3.81/4.01  thf('73', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 3.81/4.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.81/4.01  thf('74', plain,
% 3.81/4.01      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 3.81/4.01         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 3.81/4.01      inference('sup-', [status(thm)], ['72', '73'])).
% 3.81/4.01  thf('75', plain,
% 3.81/4.01      (![X31 : $i]: ((k2_zfmisc_1 @ X31 @ k1_xboole_0) = (k1_xboole_0))),
% 3.81/4.01      inference('simplify', [status(thm)], ['22'])).
% 3.81/4.01  thf('76', plain,
% 3.81/4.01      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 3.81/4.01      inference('demod', [status(thm)], ['74', '75'])).
% 3.81/4.01  thf('77', plain, (((r1_tarski @ sk_A @ sk_C_1))),
% 3.81/4.01      inference('simplify', [status(thm)], ['76'])).
% 3.81/4.01  thf('78', plain,
% 3.81/4.01      (~ ((r1_tarski @ sk_B_1 @ sk_D)) | ~ ((r1_tarski @ sk_A @ sk_C_1))),
% 3.81/4.01      inference('split', [status(esa)], ['45'])).
% 3.81/4.01  thf('79', plain, (~ ((r1_tarski @ sk_B_1 @ sk_D))),
% 3.81/4.01      inference('sat_resolution*', [status(thm)], ['77', '78'])).
% 3.81/4.01  thf('80', plain, (~ (r1_tarski @ sk_B_1 @ sk_D)),
% 3.81/4.01      inference('simpl_trail', [status(thm)], ['46', '79'])).
% 3.81/4.01  thf('81', plain, (((sk_A) = (k1_xboole_0))),
% 3.81/4.01      inference('clc', [status(thm)], ['44', '80'])).
% 3.81/4.01  thf('82', plain,
% 3.81/4.01      (![X32 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X32) = (k1_xboole_0))),
% 3.81/4.01      inference('simplify', [status(thm)], ['52'])).
% 3.81/4.01  thf('83', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 3.81/4.01      inference('demod', [status(thm)], ['0', '81', '82'])).
% 3.81/4.01  thf('84', plain, ($false), inference('simplify', [status(thm)], ['83'])).
% 3.81/4.01  
% 3.81/4.01  % SZS output end Refutation
% 3.81/4.01  
% 3.81/4.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
