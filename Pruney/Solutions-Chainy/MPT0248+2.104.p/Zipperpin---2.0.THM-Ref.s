%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1OIayVE27H

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:33 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 287 expanded)
%              Number of leaves         :   27 (  86 expanded)
%              Depth                    :   23
%              Number of atoms          :  892 (3286 expanded)
%              Number of equality atoms :  147 ( 656 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X49: $i,X50: $i] :
      ( r1_tarski @ ( k1_tarski @ X49 ) @ ( k2_tarski @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_3 ) @ ( k2_tarski @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('3',plain,(
    ! [X19: $i] :
      ( r1_tarski @ k1_xboole_0 @ X19 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ X39 @ X40 )
      | ( r1_tarski @ ( k2_xboole_0 @ X39 @ X41 ) @ ( k2_xboole_0 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('6',plain,(
    ! [X27: $i] :
      ( r1_xboole_0 @ X27 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t72_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf('8',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X29 = X28 )
      | ~ ( r1_xboole_0 @ X29 @ X30 )
      | ( ( k2_xboole_0 @ X30 @ X28 )
       != ( k2_xboole_0 @ X29 @ X31 ) )
      | ~ ( r1_xboole_0 @ X31 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
       != X0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( X12 != X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X20: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X22 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('14',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X32 @ X33 ) @ X33 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
       != X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference(demod,[status(thm)],['9','15'])).

thf('17',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
        = X1 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','18'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C_3 @ ( k2_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','21'])).

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

thf('23',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X47
        = ( k2_tarski @ X45 @ X46 ) )
      | ( X47
        = ( k1_tarski @ X46 ) )
      | ( X47
        = ( k1_tarski @ X45 ) )
      | ( X47 = k1_xboole_0 )
      | ~ ( r1_tarski @ X47 @ ( k2_tarski @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( sk_C_3 = k1_xboole_0 )
      | ( sk_C_3
        = ( k1_tarski @ sk_A ) )
      | ( sk_C_3
        = ( k1_tarski @ X0 ) )
      | ( sk_C_3
        = ( k2_tarski @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_3 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_C_3 != k1_xboole_0 )
   <= ( sk_C_3 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['25'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('27',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_3 ) @ ( k2_tarski @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X34: $i,X35: $i] :
      ( r1_tarski @ X34 @ ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('30',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X47
        = ( k2_tarski @ X45 @ X46 ) )
      | ( X47
        = ( k1_tarski @ X46 ) )
      | ( X47
        = ( k1_tarski @ X45 ) )
      | ( X47 = k1_xboole_0 )
      | ~ ( r1_tarski @ X47 @ ( k2_tarski @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( sk_B
        = ( k1_tarski @ sk_A ) )
      | ( sk_B
        = ( k1_tarski @ X0 ) )
      | ( sk_B
        = ( k2_tarski @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( sk_B != sk_B )
        | ( sk_B
          = ( k2_tarski @ sk_A @ X0 ) )
        | ( sk_B
          = ( k1_tarski @ X0 ) )
        | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( sk_B = k1_xboole_0 )
        | ( sk_B
          = ( k1_tarski @ X0 ) )
        | ( sk_B
          = ( k2_tarski @ sk_A @ X0 ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( sk_B
        = ( k1_tarski @ sk_A ) )
      | ( sk_B
        = ( k1_tarski @ sk_A ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','37'])).

thf('39',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_B
        = ( k1_tarski @ sk_A ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('41',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_3
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_C_3
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_3
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_C_3
     != ( k2_xboole_0 @ sk_B @ sk_C_3 ) )
   <= ( sk_C_3
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_C_3
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('49',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_3
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( sk_C_3
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('52',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('53',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    sk_C_3
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['48','50','54'])).

thf('56',plain,(
    sk_C_3
 != ( k2_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(simpl_trail,[status(thm)],['47','55'])).

thf('57',plain,
    ( ( sk_C_3 != sk_C_3 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','56'])).

thf('58',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_C_3 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('60',plain,(
    sk_C_3 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['58','59'])).

thf('61',plain,(
    sk_C_3 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['26','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( sk_C_3
        = ( k1_tarski @ sk_A ) )
      | ( sk_C_3
        = ( k1_tarski @ X0 ) )
      | ( sk_C_3
        = ( k2_tarski @ sk_A @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','61'])).

thf('63',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('64',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('65',plain,(
    ! [X49: $i,X50: $i] :
      ( r1_tarski @ ( k1_tarski @ X49 ) @ ( k2_tarski @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('66',plain,(
    ! [X20: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X22 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('68',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('70',plain,(
    ! [X23: $i] :
      ( ( k4_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X1 )
      = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X0 )
      = ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['64','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','72'])).

thf('74',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k3_xboole_0 @ sk_C_3 @ ( k1_tarski @ sk_A ) ) )
    | ( sk_C_3
      = ( k1_tarski @ sk_A ) )
    | ( sk_C_3
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['62','73'])).

thf('75',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','18'])).

thf('78',plain,(
    ! [X20: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X22 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X23: $i] :
      ( ( k4_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( k2_xboole_0 @ sk_B @ sk_C_3 )
      = sk_C_3 )
    | ( sk_C_3
      = ( k2_xboole_0 @ sk_B @ sk_C_3 ) )
    | ( sk_C_3
      = ( k2_xboole_0 @ sk_B @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['74','75','76','83','84','85'])).

thf('87',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C_3 )
    = sk_C_3 ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    sk_C_3
 != ( k2_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(simpl_trail,[status(thm)],['47','55'])).

thf('89',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1OIayVE27H
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:16:03 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.20/1.39  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.20/1.39  % Solved by: fo/fo7.sh
% 1.20/1.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.39  % done 2842 iterations in 0.944s
% 1.20/1.39  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.20/1.39  % SZS output start Refutation
% 1.20/1.39  thf(sk_C_3_type, type, sk_C_3: $i).
% 1.20/1.39  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.20/1.39  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.20/1.39  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.20/1.39  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.20/1.39  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.39  thf(sk_B_type, type, sk_B: $i).
% 1.20/1.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.20/1.39  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.20/1.39  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.20/1.39  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.20/1.39  thf(t43_zfmisc_1, conjecture,
% 1.20/1.39    (![A:$i,B:$i,C:$i]:
% 1.20/1.39     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.20/1.39          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.20/1.39          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.20/1.39          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.20/1.39  thf(zf_stmt_0, negated_conjecture,
% 1.20/1.39    (~( ![A:$i,B:$i,C:$i]:
% 1.20/1.39        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.20/1.39             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.20/1.39             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.20/1.39             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.20/1.39    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 1.20/1.39  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_3))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf(t12_zfmisc_1, axiom,
% 1.20/1.39    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 1.20/1.39  thf('1', plain,
% 1.20/1.39      (![X49 : $i, X50 : $i]:
% 1.20/1.39         (r1_tarski @ (k1_tarski @ X49) @ (k2_tarski @ X49 @ X50))),
% 1.20/1.39      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 1.20/1.39  thf('2', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C_3) @ (k2_tarski @ sk_A @ X0))),
% 1.20/1.39      inference('sup+', [status(thm)], ['0', '1'])).
% 1.20/1.39  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.20/1.39  thf('3', plain, (![X19 : $i]: (r1_tarski @ k1_xboole_0 @ X19)),
% 1.20/1.39      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.20/1.39  thf(t9_xboole_1, axiom,
% 1.20/1.39    (![A:$i,B:$i,C:$i]:
% 1.20/1.39     ( ( r1_tarski @ A @ B ) =>
% 1.20/1.39       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.20/1.39  thf('4', plain,
% 1.20/1.39      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.20/1.39         (~ (r1_tarski @ X39 @ X40)
% 1.20/1.39          | (r1_tarski @ (k2_xboole_0 @ X39 @ X41) @ (k2_xboole_0 @ X40 @ X41)))),
% 1.20/1.39      inference('cnf', [status(esa)], [t9_xboole_1])).
% 1.20/1.39  thf('5', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i]:
% 1.20/1.39         (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ 
% 1.20/1.39          (k2_xboole_0 @ X0 @ X1))),
% 1.20/1.39      inference('sup-', [status(thm)], ['3', '4'])).
% 1.20/1.39  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.20/1.39  thf('6', plain, (![X27 : $i]: (r1_xboole_0 @ X27 @ k1_xboole_0)),
% 1.20/1.39      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.20/1.39  thf(t1_boole, axiom,
% 1.20/1.39    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.20/1.39  thf('7', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.20/1.39      inference('cnf', [status(esa)], [t1_boole])).
% 1.20/1.39  thf(t72_xboole_1, axiom,
% 1.20/1.39    (![A:$i,B:$i,C:$i,D:$i]:
% 1.20/1.39     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 1.20/1.39         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 1.20/1.39       ( ( C ) = ( B ) ) ))).
% 1.20/1.39  thf('8', plain,
% 1.20/1.39      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.20/1.39         (((X29) = (X28))
% 1.20/1.39          | ~ (r1_xboole_0 @ X29 @ X30)
% 1.20/1.39          | ((k2_xboole_0 @ X30 @ X28) != (k2_xboole_0 @ X29 @ X31))
% 1.20/1.39          | ~ (r1_xboole_0 @ X31 @ X28))),
% 1.20/1.39      inference('cnf', [status(esa)], [t72_xboole_1])).
% 1.20/1.39  thf('9', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.39         (((k2_xboole_0 @ X2 @ X1) != (X0))
% 1.20/1.39          | ~ (r1_xboole_0 @ k1_xboole_0 @ X1)
% 1.20/1.39          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.20/1.39          | ((X0) = (X1)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['7', '8'])).
% 1.20/1.39  thf(d10_xboole_0, axiom,
% 1.20/1.39    (![A:$i,B:$i]:
% 1.20/1.39     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.20/1.39  thf('10', plain,
% 1.20/1.39      (![X12 : $i, X13 : $i]: ((r1_tarski @ X12 @ X13) | ((X12) != (X13)))),
% 1.20/1.39      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.20/1.39  thf('11', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 1.20/1.39      inference('simplify', [status(thm)], ['10'])).
% 1.20/1.39  thf(t37_xboole_1, axiom,
% 1.20/1.39    (![A:$i,B:$i]:
% 1.20/1.39     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.20/1.39  thf('12', plain,
% 1.20/1.39      (![X20 : $i, X22 : $i]:
% 1.20/1.39         (((k4_xboole_0 @ X20 @ X22) = (k1_xboole_0))
% 1.20/1.39          | ~ (r1_tarski @ X20 @ X22))),
% 1.20/1.39      inference('cnf', [status(esa)], [t37_xboole_1])).
% 1.20/1.39  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.20/1.39      inference('sup-', [status(thm)], ['11', '12'])).
% 1.20/1.39  thf(t79_xboole_1, axiom,
% 1.20/1.39    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.20/1.39  thf('14', plain,
% 1.20/1.39      (![X32 : $i, X33 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X32 @ X33) @ X33)),
% 1.20/1.39      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.20/1.39  thf('15', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.20/1.39      inference('sup+', [status(thm)], ['13', '14'])).
% 1.20/1.39  thf('16', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.39         (((k2_xboole_0 @ X2 @ X1) != (X0))
% 1.20/1.39          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.20/1.39          | ((X0) = (X1)))),
% 1.20/1.39      inference('demod', [status(thm)], ['9', '15'])).
% 1.20/1.39  thf('17', plain,
% 1.20/1.39      (![X1 : $i, X2 : $i]:
% 1.20/1.39         (((k2_xboole_0 @ X2 @ X1) = (X1))
% 1.20/1.39          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X2))),
% 1.20/1.39      inference('simplify', [status(thm)], ['16'])).
% 1.20/1.39  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.20/1.39      inference('sup-', [status(thm)], ['6', '17'])).
% 1.20/1.39  thf('19', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 1.20/1.39      inference('demod', [status(thm)], ['5', '18'])).
% 1.20/1.39  thf(t1_xboole_1, axiom,
% 1.20/1.39    (![A:$i,B:$i,C:$i]:
% 1.20/1.39     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.20/1.39       ( r1_tarski @ A @ C ) ))).
% 1.20/1.39  thf('20', plain,
% 1.20/1.39      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.20/1.39         (~ (r1_tarski @ X16 @ X17)
% 1.20/1.39          | ~ (r1_tarski @ X17 @ X18)
% 1.20/1.39          | (r1_tarski @ X16 @ X18))),
% 1.20/1.39      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.20/1.39  thf('21', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.39         ((r1_tarski @ X0 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.20/1.39      inference('sup-', [status(thm)], ['19', '20'])).
% 1.20/1.39  thf('22', plain,
% 1.20/1.39      (![X0 : $i]: (r1_tarski @ sk_C_3 @ (k2_tarski @ sk_A @ X0))),
% 1.20/1.39      inference('sup-', [status(thm)], ['2', '21'])).
% 1.20/1.39  thf(l45_zfmisc_1, axiom,
% 1.20/1.39    (![A:$i,B:$i,C:$i]:
% 1.20/1.39     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 1.20/1.39       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 1.20/1.39            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 1.20/1.39  thf('23', plain,
% 1.20/1.39      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.20/1.39         (((X47) = (k2_tarski @ X45 @ X46))
% 1.20/1.39          | ((X47) = (k1_tarski @ X46))
% 1.20/1.39          | ((X47) = (k1_tarski @ X45))
% 1.20/1.39          | ((X47) = (k1_xboole_0))
% 1.20/1.39          | ~ (r1_tarski @ X47 @ (k2_tarski @ X45 @ X46)))),
% 1.20/1.39      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 1.20/1.39  thf('24', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (((sk_C_3) = (k1_xboole_0))
% 1.20/1.39          | ((sk_C_3) = (k1_tarski @ sk_A))
% 1.20/1.39          | ((sk_C_3) = (k1_tarski @ X0))
% 1.20/1.39          | ((sk_C_3) = (k2_tarski @ sk_A @ X0)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['22', '23'])).
% 1.20/1.39  thf('25', plain,
% 1.20/1.39      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_3) != (k1_xboole_0)))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('26', plain,
% 1.20/1.39      ((((sk_C_3) != (k1_xboole_0))) <= (~ (((sk_C_3) = (k1_xboole_0))))),
% 1.20/1.39      inference('split', [status(esa)], ['25'])).
% 1.20/1.39  thf(t69_enumset1, axiom,
% 1.20/1.39    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.20/1.39  thf('27', plain,
% 1.20/1.39      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 1.20/1.39      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.20/1.39  thf('28', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C_3) @ (k2_tarski @ sk_A @ X0))),
% 1.20/1.39      inference('sup+', [status(thm)], ['0', '1'])).
% 1.20/1.39  thf(t7_xboole_1, axiom,
% 1.20/1.39    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.20/1.39  thf('29', plain,
% 1.20/1.39      (![X34 : $i, X35 : $i]: (r1_tarski @ X34 @ (k2_xboole_0 @ X34 @ X35))),
% 1.20/1.39      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.20/1.39  thf('30', plain,
% 1.20/1.39      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.20/1.39         (~ (r1_tarski @ X16 @ X17)
% 1.20/1.39          | ~ (r1_tarski @ X17 @ X18)
% 1.20/1.39          | (r1_tarski @ X16 @ X18))),
% 1.20/1.39      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.20/1.39  thf('31', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.39         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.20/1.39      inference('sup-', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('32', plain, (![X0 : $i]: (r1_tarski @ sk_B @ (k2_tarski @ sk_A @ X0))),
% 1.20/1.39      inference('sup-', [status(thm)], ['28', '31'])).
% 1.20/1.39  thf('33', plain,
% 1.20/1.39      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.20/1.39         (((X47) = (k2_tarski @ X45 @ X46))
% 1.20/1.39          | ((X47) = (k1_tarski @ X46))
% 1.20/1.39          | ((X47) = (k1_tarski @ X45))
% 1.20/1.39          | ((X47) = (k1_xboole_0))
% 1.20/1.39          | ~ (r1_tarski @ X47 @ (k2_tarski @ X45 @ X46)))),
% 1.20/1.39      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 1.20/1.39  thf('34', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (((sk_B) = (k1_xboole_0))
% 1.20/1.39          | ((sk_B) = (k1_tarski @ sk_A))
% 1.20/1.39          | ((sk_B) = (k1_tarski @ X0))
% 1.20/1.39          | ((sk_B) = (k2_tarski @ sk_A @ X0)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['32', '33'])).
% 1.20/1.39  thf('35', plain,
% 1.20/1.39      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.20/1.39      inference('split', [status(esa)], ['25'])).
% 1.20/1.39  thf('36', plain,
% 1.20/1.39      ((![X0 : $i]:
% 1.20/1.39          (((sk_B) != (sk_B))
% 1.20/1.39           | ((sk_B) = (k2_tarski @ sk_A @ X0))
% 1.20/1.39           | ((sk_B) = (k1_tarski @ X0))
% 1.20/1.39           | ((sk_B) = (k1_xboole_0))))
% 1.20/1.39         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.20/1.39      inference('sup-', [status(thm)], ['34', '35'])).
% 1.20/1.39  thf('37', plain,
% 1.20/1.39      ((![X0 : $i]:
% 1.20/1.39          (((sk_B) = (k1_xboole_0))
% 1.20/1.39           | ((sk_B) = (k1_tarski @ X0))
% 1.20/1.39           | ((sk_B) = (k2_tarski @ sk_A @ X0))))
% 1.20/1.39         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.20/1.39      inference('simplify', [status(thm)], ['36'])).
% 1.20/1.39  thf('38', plain,
% 1.20/1.39      (((((sk_B) = (k1_tarski @ sk_A))
% 1.20/1.39         | ((sk_B) = (k1_tarski @ sk_A))
% 1.20/1.39         | ((sk_B) = (k1_xboole_0)))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.20/1.39      inference('sup+', [status(thm)], ['27', '37'])).
% 1.20/1.39  thf('39', plain,
% 1.20/1.39      (((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A))))
% 1.20/1.39         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.20/1.39      inference('simplify', [status(thm)], ['38'])).
% 1.20/1.39  thf('40', plain,
% 1.20/1.39      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.20/1.39      inference('split', [status(esa)], ['25'])).
% 1.20/1.39  thf('41', plain,
% 1.20/1.39      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.20/1.39      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 1.20/1.39  thf('42', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.20/1.39      inference('sup-', [status(thm)], ['6', '17'])).
% 1.20/1.39  thf('43', plain,
% 1.20/1.39      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 1.20/1.39         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.20/1.39      inference('sup+', [status(thm)], ['41', '42'])).
% 1.20/1.39  thf('44', plain,
% 1.20/1.39      ((((sk_B) != (k1_xboole_0)) | ((sk_C_3) != (k1_tarski @ sk_A)))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('45', plain,
% 1.20/1.39      ((((sk_C_3) != (k1_tarski @ sk_A)))
% 1.20/1.39         <= (~ (((sk_C_3) = (k1_tarski @ sk_A))))),
% 1.20/1.39      inference('split', [status(esa)], ['44'])).
% 1.20/1.39  thf('46', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_3))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('47', plain,
% 1.20/1.39      ((((sk_C_3) != (k2_xboole_0 @ sk_B @ sk_C_3)))
% 1.20/1.39         <= (~ (((sk_C_3) = (k1_tarski @ sk_A))))),
% 1.20/1.39      inference('demod', [status(thm)], ['45', '46'])).
% 1.20/1.39  thf('48', plain,
% 1.20/1.39      (~ (((sk_C_3) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 1.20/1.39      inference('split', [status(esa)], ['44'])).
% 1.20/1.39  thf('49', plain,
% 1.20/1.39      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_3) != (k1_tarski @ sk_A)))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('50', plain,
% 1.20/1.39      (~ (((sk_C_3) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 1.20/1.39      inference('split', [status(esa)], ['49'])).
% 1.20/1.39  thf('51', plain,
% 1.20/1.39      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.20/1.39      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 1.20/1.39  thf('52', plain,
% 1.20/1.39      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.20/1.39      inference('split', [status(esa)], ['44'])).
% 1.20/1.39  thf('53', plain,
% 1.20/1.39      ((((sk_B) != (sk_B)))
% 1.20/1.39         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.20/1.39      inference('sup-', [status(thm)], ['51', '52'])).
% 1.20/1.39  thf('54', plain,
% 1.20/1.39      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 1.20/1.39      inference('simplify', [status(thm)], ['53'])).
% 1.20/1.39  thf('55', plain, (~ (((sk_C_3) = (k1_tarski @ sk_A)))),
% 1.20/1.39      inference('sat_resolution*', [status(thm)], ['48', '50', '54'])).
% 1.20/1.39  thf('56', plain, (((sk_C_3) != (k2_xboole_0 @ sk_B @ sk_C_3))),
% 1.20/1.39      inference('simpl_trail', [status(thm)], ['47', '55'])).
% 1.20/1.39  thf('57', plain,
% 1.20/1.39      ((((sk_C_3) != (sk_C_3))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.20/1.39      inference('sup-', [status(thm)], ['43', '56'])).
% 1.20/1.39  thf('58', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 1.20/1.39      inference('simplify', [status(thm)], ['57'])).
% 1.20/1.39  thf('59', plain,
% 1.20/1.39      (~ (((sk_C_3) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 1.20/1.39      inference('split', [status(esa)], ['25'])).
% 1.20/1.39  thf('60', plain, (~ (((sk_C_3) = (k1_xboole_0)))),
% 1.20/1.39      inference('sat_resolution*', [status(thm)], ['58', '59'])).
% 1.20/1.39  thf('61', plain, (((sk_C_3) != (k1_xboole_0))),
% 1.20/1.39      inference('simpl_trail', [status(thm)], ['26', '60'])).
% 1.20/1.39  thf('62', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (((sk_C_3) = (k1_tarski @ sk_A))
% 1.20/1.39          | ((sk_C_3) = (k1_tarski @ X0))
% 1.20/1.39          | ((sk_C_3) = (k2_tarski @ sk_A @ X0)))),
% 1.20/1.39      inference('simplify_reflect-', [status(thm)], ['24', '61'])).
% 1.20/1.39  thf('63', plain,
% 1.20/1.39      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 1.20/1.39      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.20/1.39  thf('64', plain,
% 1.20/1.39      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 1.20/1.39      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.20/1.39  thf('65', plain,
% 1.20/1.39      (![X49 : $i, X50 : $i]:
% 1.20/1.39         (r1_tarski @ (k1_tarski @ X49) @ (k2_tarski @ X49 @ X50))),
% 1.20/1.39      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 1.20/1.39  thf('66', plain,
% 1.20/1.39      (![X20 : $i, X22 : $i]:
% 1.20/1.39         (((k4_xboole_0 @ X20 @ X22) = (k1_xboole_0))
% 1.20/1.39          | ~ (r1_tarski @ X20 @ X22))),
% 1.20/1.39      inference('cnf', [status(esa)], [t37_xboole_1])).
% 1.20/1.39  thf('67', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i]:
% 1.20/1.39         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 1.20/1.39           = (k1_xboole_0))),
% 1.20/1.39      inference('sup-', [status(thm)], ['65', '66'])).
% 1.20/1.39  thf(t48_xboole_1, axiom,
% 1.20/1.39    (![A:$i,B:$i]:
% 1.20/1.39     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.20/1.39  thf('68', plain,
% 1.20/1.39      (![X24 : $i, X25 : $i]:
% 1.20/1.39         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 1.20/1.39           = (k3_xboole_0 @ X24 @ X25))),
% 1.20/1.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.20/1.39  thf('69', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i]:
% 1.20/1.39         ((k4_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0)
% 1.20/1.39           = (k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))),
% 1.20/1.39      inference('sup+', [status(thm)], ['67', '68'])).
% 1.20/1.39  thf(t3_boole, axiom,
% 1.20/1.39    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.20/1.39  thf('70', plain, (![X23 : $i]: ((k4_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 1.20/1.39      inference('cnf', [status(esa)], [t3_boole])).
% 1.20/1.39  thf('71', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i]:
% 1.20/1.39         ((k1_tarski @ X1)
% 1.20/1.39           = (k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))),
% 1.20/1.39      inference('demod', [status(thm)], ['69', '70'])).
% 1.20/1.39  thf('72', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i]:
% 1.20/1.39         ((k1_tarski @ X0)
% 1.20/1.39           = (k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X0 @ X1)))),
% 1.20/1.39      inference('sup+', [status(thm)], ['64', '71'])).
% 1.20/1.39  thf('73', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         ((k1_tarski @ X0)
% 1.20/1.39           = (k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0)))),
% 1.20/1.39      inference('sup+', [status(thm)], ['63', '72'])).
% 1.20/1.39  thf('74', plain,
% 1.20/1.39      ((((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_C_3 @ (k1_tarski @ sk_A)))
% 1.20/1.39        | ((sk_C_3) = (k1_tarski @ sk_A))
% 1.20/1.39        | ((sk_C_3) = (k1_tarski @ sk_A)))),
% 1.20/1.39      inference('sup+', [status(thm)], ['62', '73'])).
% 1.20/1.39  thf('75', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_3))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('76', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_3))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('77', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 1.20/1.39      inference('demod', [status(thm)], ['5', '18'])).
% 1.20/1.39  thf('78', plain,
% 1.20/1.39      (![X20 : $i, X22 : $i]:
% 1.20/1.39         (((k4_xboole_0 @ X20 @ X22) = (k1_xboole_0))
% 1.20/1.39          | ~ (r1_tarski @ X20 @ X22))),
% 1.20/1.39      inference('cnf', [status(esa)], [t37_xboole_1])).
% 1.20/1.39  thf('79', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i]:
% 1.20/1.39         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.20/1.39      inference('sup-', [status(thm)], ['77', '78'])).
% 1.20/1.39  thf('80', plain,
% 1.20/1.39      (![X24 : $i, X25 : $i]:
% 1.20/1.39         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 1.20/1.39           = (k3_xboole_0 @ X24 @ X25))),
% 1.20/1.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.20/1.39  thf('81', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i]:
% 1.20/1.39         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 1.20/1.39           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.20/1.39      inference('sup+', [status(thm)], ['79', '80'])).
% 1.20/1.39  thf('82', plain, (![X23 : $i]: ((k4_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 1.20/1.39      inference('cnf', [status(esa)], [t3_boole])).
% 1.20/1.39  thf('83', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i]:
% 1.20/1.39         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.20/1.39      inference('demod', [status(thm)], ['81', '82'])).
% 1.20/1.39  thf('84', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_3))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('85', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_3))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('86', plain,
% 1.20/1.39      ((((k2_xboole_0 @ sk_B @ sk_C_3) = (sk_C_3))
% 1.20/1.39        | ((sk_C_3) = (k2_xboole_0 @ sk_B @ sk_C_3))
% 1.20/1.39        | ((sk_C_3) = (k2_xboole_0 @ sk_B @ sk_C_3)))),
% 1.20/1.39      inference('demod', [status(thm)], ['74', '75', '76', '83', '84', '85'])).
% 1.20/1.39  thf('87', plain, (((k2_xboole_0 @ sk_B @ sk_C_3) = (sk_C_3))),
% 1.20/1.39      inference('simplify', [status(thm)], ['86'])).
% 1.20/1.39  thf('88', plain, (((sk_C_3) != (k2_xboole_0 @ sk_B @ sk_C_3))),
% 1.20/1.39      inference('simpl_trail', [status(thm)], ['47', '55'])).
% 1.20/1.39  thf('89', plain, ($false),
% 1.20/1.39      inference('simplify_reflect-', [status(thm)], ['87', '88'])).
% 1.20/1.39  
% 1.20/1.39  % SZS output end Refutation
% 1.20/1.39  
% 1.20/1.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
