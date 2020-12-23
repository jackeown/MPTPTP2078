%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XL0UwTO8hf

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 445 expanded)
%              Number of leaves         :   24 ( 119 expanded)
%              Depth                    :   23
%              Number of atoms          : 1129 (6144 expanded)
%              Number of equality atoms :  203 (1203 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t75_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) )
        = k1_xboole_0 )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) )
          = k1_xboole_0 )
      <=> ~ ( ( A != k1_xboole_0 )
            & ( A
             != ( k1_tarski @ B ) )
            & ( A
             != ( k1_tarski @ C ) )
            & ( A
             != ( k2_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_zfmisc_1])).

thf('0',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X53 @ X54 ) )
      = ( k2_xboole_0 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('7',plain,(
    ! [X55: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X55 ) )
      = X55 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
     != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( ( k4_xboole_0 @ X6 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('34',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

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

thf('36',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X51
        = ( k2_tarski @ X49 @ X50 ) )
      | ( X51
        = ( k1_tarski @ X50 ) )
      | ( X51
        = ( k1_tarski @ X49 ) )
      | ( X51 = k1_xboole_0 )
      | ~ ( r1_tarski @ X51 @ ( k2_tarski @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('37',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('39',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
   <= ( sk_A
     != ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['30'])).

thf('42',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['28'])).

thf('45',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_A != k1_xboole_0 )
      & ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','26','27','29','31','49'])).

thf('51',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','50'])).

thf('52',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_C ) )
   <= ( sk_A
      = ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['21'])).

thf('53',plain,(
    ! [X49: $i,X51: $i,X52: $i] :
      ( ( r1_tarski @ X51 @ ( k2_tarski @ X49 @ X52 ) )
      | ( X51 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('54',plain,(
    ! [X49: $i,X52: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X49 @ X52 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('59',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('64',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('67',plain,
    ( ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','26','27','29','31','49'])).

thf('69',plain,
    ( ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,(
    sk_A != k1_xboole_0 ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A
     != ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['30'])).

thf('73',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('74',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['21'])).

thf('75',plain,(
    ! [X49: $i,X51: $i,X52: $i] :
      ( ( r1_tarski @ X51 @ ( k2_tarski @ X49 @ X52 ) )
      | ( X51
       != ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('76',plain,(
    ! [X49: $i,X52: $i] :
      ( r1_tarski @ ( k1_tarski @ X49 ) @ ( k2_tarski @ X49 @ X52 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ X0 ) )
        = k1_xboole_0 )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['74','78'])).

thf('80',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','50'])).

thf('81',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('84',plain,
    ( sk_A
    = ( k1_tarski @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['71','3','26','27','29','72','73','82','83'])).

thf('85',plain,
    ( sk_A
    = ( k1_tarski @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['52','84'])).

thf('86',plain,(
    ! [X49: $i,X51: $i,X52: $i] :
      ( ( r1_tarski @ X51 @ ( k2_tarski @ X49 @ X52 ) )
      | ( X51
       != ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('87',plain,(
    ! [X49: $i,X52: $i] :
      ( r1_tarski @ ( k1_tarski @ X52 ) @ ( k2_tarski @ X49 @ X52 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ X0 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['85','89'])).

thf('91',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['51','90'])).

thf('92',plain,(
    $false ),
    inference(simplify,[status(thm)],['91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XL0UwTO8hf
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:42:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.59  % Solved by: fo/fo7.sh
% 0.22/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.59  % done 421 iterations in 0.132s
% 0.22/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.59  % SZS output start Refutation
% 0.22/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.59  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.59  thf(t75_zfmisc_1, conjecture,
% 0.22/0.59    (![A:$i,B:$i,C:$i]:
% 0.22/0.59     ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.59       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.22/0.59            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.22/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.59        ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.59          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.22/0.59               ( ( A ) != ( k1_tarski @ C ) ) & 
% 0.22/0.59               ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ) )),
% 0.22/0.59    inference('cnf.neg', [status(esa)], [t75_zfmisc_1])).
% 0.22/0.59  thf('0', plain,
% 0.22/0.59      ((((sk_A) != (k1_xboole_0))
% 0.22/0.59        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('1', plain,
% 0.22/0.59      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.22/0.59         <= (~
% 0.22/0.59             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.22/0.59      inference('split', [status(esa)], ['0'])).
% 0.22/0.59  thf('2', plain,
% 0.22/0.59      ((((sk_A) != (k2_tarski @ sk_B @ sk_C))
% 0.22/0.59        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('3', plain,
% 0.22/0.59      (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) | 
% 0.22/0.59       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.22/0.59      inference('split', [status(esa)], ['2'])).
% 0.22/0.59  thf(t69_enumset1, axiom,
% 0.22/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.59  thf('4', plain, (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.22/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.59  thf(l51_zfmisc_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.59  thf('5', plain,
% 0.22/0.59      (![X53 : $i, X54 : $i]:
% 0.22/0.59         ((k3_tarski @ (k2_tarski @ X53 @ X54)) = (k2_xboole_0 @ X53 @ X54))),
% 0.22/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.59  thf('6', plain,
% 0.22/0.59      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['4', '5'])).
% 0.22/0.59  thf(t31_zfmisc_1, axiom,
% 0.22/0.59    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.22/0.59  thf('7', plain, (![X55 : $i]: ((k3_tarski @ (k1_tarski @ X55)) = (X55))),
% 0.22/0.59      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.22/0.59  thf('8', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.22/0.59      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.59  thf(t95_xboole_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( k3_xboole_0 @ A @ B ) =
% 0.22/0.59       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.22/0.59  thf('9', plain,
% 0.22/0.59      (![X19 : $i, X20 : $i]:
% 0.22/0.59         ((k3_xboole_0 @ X19 @ X20)
% 0.22/0.59           = (k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ 
% 0.22/0.59              (k2_xboole_0 @ X19 @ X20)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.22/0.59  thf(t91_xboole_1, axiom,
% 0.22/0.59    (![A:$i,B:$i,C:$i]:
% 0.22/0.59     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.59       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.22/0.59  thf('10', plain,
% 0.22/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.59         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.22/0.59           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.59  thf('11', plain,
% 0.22/0.59      (![X19 : $i, X20 : $i]:
% 0.22/0.59         ((k3_xboole_0 @ X19 @ X20)
% 0.22/0.59           = (k5_xboole_0 @ X19 @ 
% 0.22/0.59              (k5_xboole_0 @ X20 @ (k2_xboole_0 @ X19 @ X20))))),
% 0.22/0.59      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.59  thf('12', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k3_xboole_0 @ X0 @ X0)
% 0.22/0.59           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.22/0.59      inference('sup+', [status(thm)], ['8', '11'])).
% 0.22/0.59  thf(t92_xboole_1, axiom,
% 0.22/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.59  thf('13', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.22/0.59      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.59  thf('14', plain,
% 0.22/0.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.59  thf(t5_boole, axiom,
% 0.22/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.59  thf('15', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.22/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.59  thf('16', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.59      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.59  thf(t100_xboole_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.59  thf('17', plain,
% 0.22/0.59      (![X2 : $i, X3 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X2 @ X3)
% 0.22/0.59           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.59  thf('18', plain,
% 0.22/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.22/0.59  thf('19', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.22/0.59      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.59  thf('20', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['18', '19'])).
% 0.22/0.59  thf('21', plain,
% 0.22/0.59      ((((sk_A) = (k2_tarski @ sk_B @ sk_C))
% 0.22/0.59        | ((sk_A) = (k1_tarski @ sk_C))
% 0.22/0.59        | ((sk_A) = (k1_tarski @ sk_B))
% 0.22/0.59        | ((sk_A) = (k1_xboole_0))
% 0.22/0.59        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('22', plain,
% 0.22/0.59      ((((sk_A) = (k2_tarski @ sk_B @ sk_C)))
% 0.22/0.59         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.22/0.59      inference('split', [status(esa)], ['21'])).
% 0.22/0.59  thf('23', plain,
% 0.22/0.59      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.22/0.59         <= (~
% 0.22/0.59             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.22/0.59      inference('split', [status(esa)], ['0'])).
% 0.22/0.59  thf('24', plain,
% 0.22/0.59      ((((k4_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0)))
% 0.22/0.59         <= (~
% 0.22/0.59             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.22/0.59             (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.59  thf('25', plain,
% 0.22/0.59      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.59         <= (~
% 0.22/0.59             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.22/0.59             (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['20', '24'])).
% 0.22/0.59  thf('26', plain,
% 0.22/0.59      (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) | 
% 0.22/0.59       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.22/0.59      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.59  thf('27', plain,
% 0.22/0.59      (~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.22/0.59       ~ (((sk_A) = (k1_xboole_0)))),
% 0.22/0.59      inference('split', [status(esa)], ['0'])).
% 0.22/0.59  thf('28', plain,
% 0.22/0.59      ((((sk_A) != (k1_tarski @ sk_B))
% 0.22/0.59        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('29', plain,
% 0.22/0.59      (~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.22/0.59       ~ (((sk_A) = (k1_tarski @ sk_B)))),
% 0.22/0.59      inference('split', [status(esa)], ['28'])).
% 0.22/0.59  thf('30', plain,
% 0.22/0.59      ((((sk_A) != (k1_tarski @ sk_C))
% 0.22/0.59        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('31', plain,
% 0.22/0.59      (~ (((sk_A) = (k1_tarski @ sk_C))) | 
% 0.22/0.59       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.22/0.59      inference('split', [status(esa)], ['30'])).
% 0.22/0.59  thf('32', plain,
% 0.22/0.59      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))
% 0.22/0.59         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.22/0.59      inference('split', [status(esa)], ['21'])).
% 0.22/0.59  thf(t37_xboole_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.59  thf('33', plain,
% 0.22/0.59      (![X6 : $i, X7 : $i]:
% 0.22/0.59         ((r1_tarski @ X6 @ X7) | ((k4_xboole_0 @ X6 @ X7) != (k1_xboole_0)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.22/0.59  thf('34', plain,
% 0.22/0.59      (((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.59         | (r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C))))
% 0.22/0.59         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.59  thf('35', plain,
% 0.22/0.59      (((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))
% 0.22/0.59         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.22/0.59      inference('simplify', [status(thm)], ['34'])).
% 0.22/0.59  thf(l45_zfmisc_1, axiom,
% 0.22/0.59    (![A:$i,B:$i,C:$i]:
% 0.22/0.59     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.22/0.59       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.22/0.59            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.22/0.59  thf('36', plain,
% 0.22/0.59      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.22/0.59         (((X51) = (k2_tarski @ X49 @ X50))
% 0.22/0.59          | ((X51) = (k1_tarski @ X50))
% 0.22/0.59          | ((X51) = (k1_tarski @ X49))
% 0.22/0.59          | ((X51) = (k1_xboole_0))
% 0.22/0.59          | ~ (r1_tarski @ X51 @ (k2_tarski @ X49 @ X50)))),
% 0.22/0.59      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.22/0.59  thf('37', plain,
% 0.22/0.59      (((((sk_A) = (k1_xboole_0))
% 0.22/0.59         | ((sk_A) = (k1_tarski @ sk_B))
% 0.22/0.59         | ((sk_A) = (k1_tarski @ sk_C))
% 0.22/0.59         | ((sk_A) = (k2_tarski @ sk_B @ sk_C))))
% 0.22/0.59         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.59  thf('38', plain,
% 0.22/0.59      ((((sk_A) != (k2_tarski @ sk_B @ sk_C)))
% 0.22/0.59         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.22/0.59      inference('split', [status(esa)], ['2'])).
% 0.22/0.59  thf('39', plain,
% 0.22/0.59      (((((sk_A) != (sk_A))
% 0.22/0.59         | ((sk_A) = (k1_tarski @ sk_C))
% 0.22/0.59         | ((sk_A) = (k1_tarski @ sk_B))
% 0.22/0.59         | ((sk_A) = (k1_xboole_0))))
% 0.22/0.59         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.22/0.59             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.59  thf('40', plain,
% 0.22/0.59      (((((sk_A) = (k1_xboole_0))
% 0.22/0.59         | ((sk_A) = (k1_tarski @ sk_B))
% 0.22/0.59         | ((sk_A) = (k1_tarski @ sk_C))))
% 0.22/0.59         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.22/0.59             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.22/0.59      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.59  thf('41', plain,
% 0.22/0.59      ((((sk_A) != (k1_tarski @ sk_C))) <= (~ (((sk_A) = (k1_tarski @ sk_C))))),
% 0.22/0.59      inference('split', [status(esa)], ['30'])).
% 0.22/0.59  thf('42', plain,
% 0.22/0.59      (((((sk_A) != (sk_A))
% 0.22/0.59         | ((sk_A) = (k1_tarski @ sk_B))
% 0.22/0.59         | ((sk_A) = (k1_xboole_0))))
% 0.22/0.59         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.22/0.59             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.22/0.60             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.22/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.60  thf('43', plain,
% 0.22/0.60      (((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ sk_B))))
% 0.22/0.60         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.22/0.60             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.22/0.60             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.22/0.60      inference('simplify', [status(thm)], ['42'])).
% 0.22/0.60  thf('44', plain,
% 0.22/0.60      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 0.22/0.60      inference('split', [status(esa)], ['28'])).
% 0.22/0.60  thf('45', plain,
% 0.22/0.60      (((((sk_A) != (sk_A)) | ((sk_A) = (k1_xboole_0))))
% 0.22/0.60         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.22/0.60             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.22/0.60             ~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.22/0.60             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.22/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.60  thf('46', plain,
% 0.22/0.60      ((((sk_A) = (k1_xboole_0)))
% 0.22/0.60         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.22/0.60             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.22/0.60             ~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.22/0.60             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.22/0.60      inference('simplify', [status(thm)], ['45'])).
% 0.22/0.60  thf('47', plain,
% 0.22/0.60      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.22/0.60      inference('split', [status(esa)], ['0'])).
% 0.22/0.60  thf('48', plain,
% 0.22/0.60      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.60         <= (~ (((sk_A) = (k1_xboole_0))) & 
% 0.22/0.60             ~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.22/0.60             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.22/0.60             ~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.22/0.60             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.22/0.60      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.60  thf('49', plain,
% 0.22/0.60      ((((sk_A) = (k1_tarski @ sk_B))) | 
% 0.22/0.60       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.22/0.60       (((sk_A) = (k1_tarski @ sk_C))) | 
% 0.22/0.60       (((sk_A) = (k2_tarski @ sk_B @ sk_C))) | (((sk_A) = (k1_xboole_0)))),
% 0.22/0.60      inference('simplify', [status(thm)], ['48'])).
% 0.22/0.60  thf('50', plain,
% 0.22/0.60      (~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.22/0.60      inference('sat_resolution*', [status(thm)],
% 0.22/0.60                ['3', '26', '27', '29', '31', '49'])).
% 0.22/0.60  thf('51', plain,
% 0.22/0.60      (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0))),
% 0.22/0.60      inference('simpl_trail', [status(thm)], ['1', '50'])).
% 0.22/0.60  thf('52', plain,
% 0.22/0.60      ((((sk_A) = (k1_tarski @ sk_C))) <= ((((sk_A) = (k1_tarski @ sk_C))))),
% 0.22/0.60      inference('split', [status(esa)], ['21'])).
% 0.22/0.60  thf('53', plain,
% 0.22/0.60      (![X49 : $i, X51 : $i, X52 : $i]:
% 0.22/0.60         ((r1_tarski @ X51 @ (k2_tarski @ X49 @ X52))
% 0.22/0.60          | ((X51) != (k1_xboole_0)))),
% 0.22/0.60      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.22/0.60  thf('54', plain,
% 0.22/0.60      (![X49 : $i, X52 : $i]:
% 0.22/0.60         (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X49 @ X52))),
% 0.22/0.60      inference('simplify', [status(thm)], ['53'])).
% 0.22/0.60  thf('55', plain,
% 0.22/0.60      (![X6 : $i, X8 : $i]:
% 0.22/0.60         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.22/0.60      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.22/0.60  thf('56', plain,
% 0.22/0.60      (![X0 : $i, X1 : $i]:
% 0.22/0.60         ((k4_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X1 @ X0)) = (k1_xboole_0))),
% 0.22/0.60      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.60  thf('57', plain,
% 0.22/0.60      (![X2 : $i, X3 : $i]:
% 0.22/0.60         ((k4_xboole_0 @ X2 @ X3)
% 0.22/0.60           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.22/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.60  thf(commutativity_k5_xboole_0, axiom,
% 0.22/0.60    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.22/0.60  thf('58', plain,
% 0.22/0.60      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.22/0.60      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.22/0.60  thf('59', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.22/0.60      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.60  thf('60', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.60      inference('sup+', [status(thm)], ['58', '59'])).
% 0.22/0.60  thf('61', plain,
% 0.22/0.60      (![X0 : $i]:
% 0.22/0.60         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.60      inference('sup+', [status(thm)], ['57', '60'])).
% 0.22/0.60  thf('62', plain,
% 0.22/0.60      (![X0 : $i, X1 : $i]:
% 0.22/0.60         ((k3_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X1 @ X0)) = (k1_xboole_0))),
% 0.22/0.60      inference('demod', [status(thm)], ['56', '61'])).
% 0.22/0.60  thf('63', plain,
% 0.22/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.22/0.60      inference('split', [status(esa)], ['21'])).
% 0.22/0.60  thf('64', plain,
% 0.22/0.60      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.22/0.60         <= (~
% 0.22/0.60             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.22/0.60      inference('split', [status(esa)], ['0'])).
% 0.22/0.60  thf('65', plain,
% 0.22/0.60      ((((k4_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_B @ sk_C))
% 0.22/0.60          != (k1_xboole_0)))
% 0.22/0.60         <= (~
% 0.22/0.60             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.22/0.60             (((sk_A) = (k1_xboole_0))))),
% 0.22/0.60      inference('sup-', [status(thm)], ['63', '64'])).
% 0.22/0.60  thf('66', plain,
% 0.22/0.60      (![X0 : $i]:
% 0.22/0.60         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.60      inference('sup+', [status(thm)], ['57', '60'])).
% 0.22/0.60  thf('67', plain,
% 0.22/0.60      ((((k3_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_B @ sk_C))
% 0.22/0.60          != (k1_xboole_0)))
% 0.22/0.60         <= (~
% 0.22/0.60             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.22/0.60             (((sk_A) = (k1_xboole_0))))),
% 0.22/0.60      inference('demod', [status(thm)], ['65', '66'])).
% 0.22/0.60  thf('68', plain,
% 0.22/0.60      (~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.22/0.60      inference('sat_resolution*', [status(thm)],
% 0.22/0.60                ['3', '26', '27', '29', '31', '49'])).
% 0.22/0.60  thf('69', plain,
% 0.22/0.60      ((((k3_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_B @ sk_C))
% 0.22/0.60          != (k1_xboole_0)))
% 0.22/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.22/0.60      inference('simpl_trail', [status(thm)], ['67', '68'])).
% 0.22/0.60  thf('70', plain,
% 0.22/0.60      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.22/0.60      inference('sup-', [status(thm)], ['62', '69'])).
% 0.22/0.60  thf('71', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.22/0.60      inference('simplify', [status(thm)], ['70'])).
% 0.22/0.60  thf('72', plain,
% 0.22/0.60      (~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.22/0.60       ~ (((sk_A) = (k1_tarski @ sk_C)))),
% 0.22/0.60      inference('split', [status(esa)], ['30'])).
% 0.22/0.60  thf('73', plain,
% 0.22/0.60      (~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.22/0.60       (((sk_A) = (k1_tarski @ sk_B))) | (((sk_A) = (k1_tarski @ sk_C))) | 
% 0.22/0.60       (((sk_A) = (k2_tarski @ sk_B @ sk_C))) | (((sk_A) = (k1_xboole_0)))),
% 0.22/0.60      inference('simplify', [status(thm)], ['48'])).
% 0.22/0.60  thf('74', plain,
% 0.22/0.60      ((((sk_A) = (k1_tarski @ sk_B))) <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.22/0.60      inference('split', [status(esa)], ['21'])).
% 0.22/0.60  thf('75', plain,
% 0.22/0.60      (![X49 : $i, X51 : $i, X52 : $i]:
% 0.22/0.60         ((r1_tarski @ X51 @ (k2_tarski @ X49 @ X52))
% 0.22/0.60          | ((X51) != (k1_tarski @ X49)))),
% 0.22/0.60      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.22/0.60  thf('76', plain,
% 0.22/0.60      (![X49 : $i, X52 : $i]:
% 0.22/0.60         (r1_tarski @ (k1_tarski @ X49) @ (k2_tarski @ X49 @ X52))),
% 0.22/0.60      inference('simplify', [status(thm)], ['75'])).
% 0.22/0.60  thf('77', plain,
% 0.22/0.60      (![X6 : $i, X8 : $i]:
% 0.22/0.60         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.22/0.60      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.22/0.60  thf('78', plain,
% 0.22/0.60      (![X0 : $i, X1 : $i]:
% 0.22/0.60         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.22/0.60           = (k1_xboole_0))),
% 0.22/0.60      inference('sup-', [status(thm)], ['76', '77'])).
% 0.22/0.60  thf('79', plain,
% 0.22/0.60      ((![X0 : $i]:
% 0.22/0.60          ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ X0)) = (k1_xboole_0)))
% 0.22/0.60         <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.22/0.60      inference('sup+', [status(thm)], ['74', '78'])).
% 0.22/0.60  thf('80', plain,
% 0.22/0.60      (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0))),
% 0.22/0.60      inference('simpl_trail', [status(thm)], ['1', '50'])).
% 0.22/0.60  thf('81', plain,
% 0.22/0.60      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.22/0.60      inference('sup-', [status(thm)], ['79', '80'])).
% 0.22/0.60  thf('82', plain, (~ (((sk_A) = (k1_tarski @ sk_B)))),
% 0.22/0.60      inference('simplify', [status(thm)], ['81'])).
% 0.22/0.60  thf('83', plain,
% 0.22/0.60      ((((sk_A) = (k1_tarski @ sk_C))) | (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.22/0.60       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.22/0.60       (((sk_A) = (k2_tarski @ sk_B @ sk_C))) | (((sk_A) = (k1_xboole_0)))),
% 0.22/0.60      inference('split', [status(esa)], ['21'])).
% 0.22/0.60  thf('84', plain, ((((sk_A) = (k1_tarski @ sk_C)))),
% 0.22/0.60      inference('sat_resolution*', [status(thm)],
% 0.22/0.60                ['71', '3', '26', '27', '29', '72', '73', '82', '83'])).
% 0.22/0.60  thf('85', plain, (((sk_A) = (k1_tarski @ sk_C))),
% 0.22/0.60      inference('simpl_trail', [status(thm)], ['52', '84'])).
% 0.22/0.60  thf('86', plain,
% 0.22/0.60      (![X49 : $i, X51 : $i, X52 : $i]:
% 0.22/0.60         ((r1_tarski @ X51 @ (k2_tarski @ X49 @ X52))
% 0.22/0.60          | ((X51) != (k1_tarski @ X52)))),
% 0.22/0.60      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.22/0.60  thf('87', plain,
% 0.22/0.60      (![X49 : $i, X52 : $i]:
% 0.22/0.60         (r1_tarski @ (k1_tarski @ X52) @ (k2_tarski @ X49 @ X52))),
% 0.22/0.60      inference('simplify', [status(thm)], ['86'])).
% 0.22/0.60  thf('88', plain,
% 0.22/0.60      (![X6 : $i, X8 : $i]:
% 0.22/0.60         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.22/0.60      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.22/0.60  thf('89', plain,
% 0.22/0.60      (![X0 : $i, X1 : $i]:
% 0.22/0.60         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.22/0.60           = (k1_xboole_0))),
% 0.22/0.60      inference('sup-', [status(thm)], ['87', '88'])).
% 0.22/0.60  thf('90', plain,
% 0.22/0.60      (![X0 : $i]:
% 0.22/0.60         ((k4_xboole_0 @ sk_A @ (k2_tarski @ X0 @ sk_C)) = (k1_xboole_0))),
% 0.22/0.60      inference('sup+', [status(thm)], ['85', '89'])).
% 0.22/0.60  thf('91', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.60      inference('demod', [status(thm)], ['51', '90'])).
% 0.22/0.60  thf('92', plain, ($false), inference('simplify', [status(thm)], ['91'])).
% 0.22/0.60  
% 0.22/0.60  % SZS output end Refutation
% 0.22/0.60  
% 0.22/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
