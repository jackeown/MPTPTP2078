%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PU0R4JhBhI

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:43 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 150 expanded)
%              Number of leaves         :   37 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  657 (1008 expanded)
%              Number of equality atoms :   67 ( 101 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t75_zfmisc_1,axiom,(
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

thf('1',plain,(
    ! [X36: $i,X38: $i,X39: $i] :
      ( ( ( k4_xboole_0 @ X38 @ ( k2_tarski @ X36 @ X39 ) )
        = k1_xboole_0 )
      | ( X38
       != ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t75_zfmisc_1])).

thf('2',plain,(
    ! [X36: $i,X39: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X36 ) @ ( k2_tarski @ X36 @ X39 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t73_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X32 @ X34 ) @ X33 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t73_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t80_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X40: $i] :
      ( r1_tarski @ ( k1_tarski @ X40 ) @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('13',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ( m1_subset_1 @ X41 @ X42 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('15',plain,(
    ! [X48: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('17',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k3_subset_1 @ X50 @ ( k3_subset_1 @ X50 @ X49 ) )
        = X49 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k3_subset_1 @ X46 @ X47 )
        = ( k4_xboole_0 @ X46 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

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

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('23',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('24',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X22 @ X23 ) @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
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
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
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

thf('31',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('36',plain,(
    ! [X36: $i,X38: $i,X39: $i] :
      ( ( ( k4_xboole_0 @ X38 @ ( k2_tarski @ X36 @ X39 ) )
        = k1_xboole_0 )
      | ( X38 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t75_zfmisc_1])).

thf('37',plain,(
    ! [X36: $i,X39: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X36 @ X39 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('42',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('46',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['34','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['22','48'])).

thf('50',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('51',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t72_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf('52',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 = X18 )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( ( k2_xboole_0 @ X20 @ X18 )
       != ( k2_xboole_0 @ X19 @ X21 ) )
      | ~ ( r1_xboole_0 @ X21 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t72_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_xboole_0 @ X2 @ X1 ) )
      | ~ ( r1_xboole_0 @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k2_xboole_0 @ X2 @ X1 ) )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','58'])).

thf(t22_subset_1,conjecture,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k2_subset_1 @ A )
        = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_subset_1])).

thf('60',plain,(
    ( k2_subset_1 @ sk_A )
 != ( k3_subset_1 @ sk_A @ ( k1_subset_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('61',plain,(
    ! [X44: $i] :
      ( ( k1_subset_1 @ X44 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('62',plain,(
    ( k2_subset_1 @ sk_A )
 != ( k3_subset_1 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('63',plain,(
    ! [X45: $i] :
      ( ( k2_subset_1 @ X45 )
      = X45 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('64',plain,(
    sk_A
 != ( k3_subset_1 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( sk_A
     != ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    sk_A != sk_A ),
    inference('sup-',[status(thm)],['18','65'])).

thf('67',plain,(
    $false ),
    inference(simplify,[status(thm)],['66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PU0R4JhBhI
% 0.15/0.38  % Computer   : n009.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 14:59:11 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.57  % Solved by: fo/fo7.sh
% 0.24/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.57  % done 567 iterations in 0.100s
% 0.24/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.57  % SZS output start Refutation
% 0.24/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.57  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.24/0.57  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.24/0.57  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.24/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.57  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.24/0.57  thf(t69_enumset1, axiom,
% 0.24/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.24/0.57  thf('0', plain, (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.24/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.57  thf(t75_zfmisc_1, axiom,
% 0.24/0.57    (![A:$i,B:$i,C:$i]:
% 0.24/0.57     ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.24/0.57       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.24/0.57            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.24/0.57  thf('1', plain,
% 0.24/0.57      (![X36 : $i, X38 : $i, X39 : $i]:
% 0.24/0.57         (((k4_xboole_0 @ X38 @ (k2_tarski @ X36 @ X39)) = (k1_xboole_0))
% 0.24/0.57          | ((X38) != (k1_tarski @ X36)))),
% 0.24/0.57      inference('cnf', [status(esa)], [t75_zfmisc_1])).
% 0.24/0.57  thf('2', plain,
% 0.24/0.57      (![X36 : $i, X39 : $i]:
% 0.24/0.57         ((k4_xboole_0 @ (k1_tarski @ X36) @ (k2_tarski @ X36 @ X39))
% 0.24/0.57           = (k1_xboole_0))),
% 0.24/0.57      inference('simplify', [status(thm)], ['1'])).
% 0.24/0.57  thf('3', plain,
% 0.24/0.57      (![X0 : $i]:
% 0.24/0.57         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.24/0.57      inference('sup+', [status(thm)], ['0', '2'])).
% 0.24/0.57  thf('4', plain, (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.24/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.57  thf(t73_zfmisc_1, axiom,
% 0.24/0.57    (![A:$i,B:$i,C:$i]:
% 0.24/0.57     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.24/0.57       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.24/0.57  thf('5', plain,
% 0.24/0.57      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.24/0.57         ((r2_hidden @ X32 @ X33)
% 0.24/0.57          | ((k4_xboole_0 @ (k2_tarski @ X32 @ X34) @ X33) != (k1_xboole_0)))),
% 0.24/0.57      inference('cnf', [status(esa)], [t73_zfmisc_1])).
% 0.24/0.57  thf('6', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]:
% 0.24/0.57         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_xboole_0))
% 0.24/0.57          | (r2_hidden @ X0 @ X1))),
% 0.24/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.57  thf('7', plain,
% 0.24/0.57      (![X0 : $i]:
% 0.24/0.57         (((k1_xboole_0) != (k1_xboole_0))
% 0.24/0.57          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['3', '6'])).
% 0.24/0.57  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.24/0.57      inference('simplify', [status(thm)], ['7'])).
% 0.24/0.57  thf(t80_zfmisc_1, axiom,
% 0.24/0.57    (![A:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.24/0.57  thf('9', plain,
% 0.24/0.57      (![X40 : $i]: (r1_tarski @ (k1_tarski @ X40) @ (k1_zfmisc_1 @ X40))),
% 0.24/0.57      inference('cnf', [status(esa)], [t80_zfmisc_1])).
% 0.24/0.57  thf(d3_tarski, axiom,
% 0.24/0.57    (![A:$i,B:$i]:
% 0.24/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.24/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.24/0.57  thf('10', plain,
% 0.24/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.24/0.57         (~ (r2_hidden @ X2 @ X3)
% 0.24/0.57          | (r2_hidden @ X2 @ X4)
% 0.24/0.57          | ~ (r1_tarski @ X3 @ X4))),
% 0.24/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.57  thf('11', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]:
% 0.24/0.57         ((r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 0.24/0.57          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.24/0.57  thf('12', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.24/0.57      inference('sup-', [status(thm)], ['8', '11'])).
% 0.24/0.57  thf(d2_subset_1, axiom,
% 0.24/0.57    (![A:$i,B:$i]:
% 0.24/0.57     ( ( ( v1_xboole_0 @ A ) =>
% 0.24/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.24/0.57       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.24/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.24/0.57  thf('13', plain,
% 0.24/0.57      (![X41 : $i, X42 : $i]:
% 0.24/0.57         (~ (r2_hidden @ X41 @ X42)
% 0.24/0.57          | (m1_subset_1 @ X41 @ X42)
% 0.24/0.57          | (v1_xboole_0 @ X42))),
% 0.24/0.57      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.24/0.57  thf('14', plain,
% 0.24/0.57      (![X0 : $i]:
% 0.24/0.57         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.24/0.57          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.57  thf(fc1_subset_1, axiom,
% 0.24/0.57    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.24/0.57  thf('15', plain, (![X48 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X48))),
% 0.24/0.57      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.24/0.57  thf('16', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.24/0.57      inference('clc', [status(thm)], ['14', '15'])).
% 0.24/0.57  thf(involutiveness_k3_subset_1, axiom,
% 0.24/0.57    (![A:$i,B:$i]:
% 0.24/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.57       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.24/0.57  thf('17', plain,
% 0.24/0.57      (![X49 : $i, X50 : $i]:
% 0.24/0.57         (((k3_subset_1 @ X50 @ (k3_subset_1 @ X50 @ X49)) = (X49))
% 0.24/0.57          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50)))),
% 0.24/0.57      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.24/0.57  thf('18', plain,
% 0.24/0.57      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.24/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.57  thf('19', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.24/0.57      inference('clc', [status(thm)], ['14', '15'])).
% 0.24/0.57  thf(d5_subset_1, axiom,
% 0.24/0.57    (![A:$i,B:$i]:
% 0.24/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.57       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.24/0.57  thf('20', plain,
% 0.24/0.57      (![X46 : $i, X47 : $i]:
% 0.24/0.57         (((k3_subset_1 @ X46 @ X47) = (k4_xboole_0 @ X46 @ X47))
% 0.24/0.57          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X46)))),
% 0.24/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.24/0.57  thf('21', plain,
% 0.24/0.57      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.24/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.24/0.57  thf(t3_xboole_0, axiom,
% 0.24/0.57    (![A:$i,B:$i]:
% 0.24/0.57     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.24/0.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.24/0.57            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.24/0.57  thf('22', plain,
% 0.24/0.57      (![X6 : $i, X7 : $i]:
% 0.24/0.57         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C_1 @ X7 @ X6) @ X6))),
% 0.24/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.24/0.57  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.24/0.57  thf('23', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 0.24/0.57      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.24/0.57  thf(t88_xboole_1, axiom,
% 0.24/0.57    (![A:$i,B:$i]:
% 0.24/0.57     ( ( r1_xboole_0 @ A @ B ) =>
% 0.24/0.57       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.24/0.57  thf('24', plain,
% 0.24/0.57      (![X22 : $i, X23 : $i]:
% 0.24/0.57         (((k4_xboole_0 @ (k2_xboole_0 @ X22 @ X23) @ X23) = (X22))
% 0.24/0.57          | ~ (r1_xboole_0 @ X22 @ X23))),
% 0.24/0.57      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.24/0.57  thf('25', plain,
% 0.24/0.57      (![X0 : $i]:
% 0.24/0.57         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0) = (X0))),
% 0.24/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.24/0.57  thf(t1_boole, axiom,
% 0.24/0.57    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.24/0.57  thf('26', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.24/0.57      inference('cnf', [status(esa)], [t1_boole])).
% 0.24/0.57  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.24/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.24/0.57  thf(t48_xboole_1, axiom,
% 0.24/0.57    (![A:$i,B:$i]:
% 0.24/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.24/0.57  thf('28', plain,
% 0.24/0.57      (![X15 : $i, X16 : $i]:
% 0.24/0.57         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.24/0.57           = (k3_xboole_0 @ X15 @ X16))),
% 0.24/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.24/0.57  thf('29', plain,
% 0.24/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.24/0.57      inference('sup+', [status(thm)], ['27', '28'])).
% 0.24/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.24/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.24/0.57  thf('30', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.24/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.24/0.57  thf(t4_xboole_0, axiom,
% 0.24/0.57    (![A:$i,B:$i]:
% 0.24/0.57     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.24/0.57            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.24/0.57  thf('31', plain,
% 0.24/0.57      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.24/0.57         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 0.24/0.57          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.24/0.57      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.24/0.57  thf('32', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.57         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.24/0.57          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.24/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.24/0.57  thf('33', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]:
% 0.24/0.57         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.24/0.57          | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.24/0.57      inference('sup-', [status(thm)], ['29', '32'])).
% 0.24/0.57  thf('34', plain,
% 0.24/0.57      (![X6 : $i, X7 : $i]:
% 0.24/0.57         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C_1 @ X7 @ X6) @ X6))),
% 0.24/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.24/0.57  thf('35', plain,
% 0.24/0.57      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.24/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.57  thf('36', plain,
% 0.24/0.57      (![X36 : $i, X38 : $i, X39 : $i]:
% 0.24/0.57         (((k4_xboole_0 @ X38 @ (k2_tarski @ X36 @ X39)) = (k1_xboole_0))
% 0.24/0.57          | ((X38) != (k1_xboole_0)))),
% 0.24/0.57      inference('cnf', [status(esa)], [t75_zfmisc_1])).
% 0.24/0.57  thf('37', plain,
% 0.24/0.57      (![X36 : $i, X39 : $i]:
% 0.24/0.57         ((k4_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X36 @ X39)) = (k1_xboole_0))),
% 0.24/0.57      inference('simplify', [status(thm)], ['36'])).
% 0.24/0.57  thf('38', plain,
% 0.24/0.57      (![X0 : $i]:
% 0.24/0.57         ((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.24/0.57      inference('sup+', [status(thm)], ['35', '37'])).
% 0.24/0.57  thf('39', plain,
% 0.24/0.57      (![X15 : $i, X16 : $i]:
% 0.24/0.57         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.24/0.57           = (k3_xboole_0 @ X15 @ X16))),
% 0.24/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.24/0.57  thf('40', plain,
% 0.24/0.57      (![X0 : $i]:
% 0.24/0.57         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.24/0.57           = (k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 0.24/0.57      inference('sup+', [status(thm)], ['38', '39'])).
% 0.24/0.57  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.24/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.24/0.57  thf('42', plain,
% 0.24/0.57      (![X0 : $i]:
% 0.24/0.57         ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 0.24/0.57      inference('demod', [status(thm)], ['40', '41'])).
% 0.24/0.57  thf('43', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.57         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.24/0.57          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.24/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.24/0.57  thf('44', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]:
% 0.24/0.57         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.24/0.57          | ~ (r1_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 0.24/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.24/0.57  thf('45', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 0.24/0.57      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.24/0.57  thf('46', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.24/0.57      inference('demod', [status(thm)], ['44', '45'])).
% 0.24/0.57  thf('47', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.24/0.57      inference('sup-', [status(thm)], ['34', '46'])).
% 0.24/0.57  thf('48', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.24/0.57      inference('demod', [status(thm)], ['33', '47'])).
% 0.24/0.57  thf('49', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.24/0.57      inference('sup-', [status(thm)], ['22', '48'])).
% 0.24/0.57  thf('50', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.24/0.57      inference('cnf', [status(esa)], [t1_boole])).
% 0.24/0.57  thf('51', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.24/0.57      inference('cnf', [status(esa)], [t1_boole])).
% 0.24/0.57  thf(t72_xboole_1, axiom,
% 0.24/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.57     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.24/0.57         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.24/0.57       ( ( C ) = ( B ) ) ))).
% 0.24/0.57  thf('52', plain,
% 0.24/0.57      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.24/0.57         (((X19) = (X18))
% 0.24/0.57          | ~ (r1_xboole_0 @ X19 @ X20)
% 0.24/0.57          | ((k2_xboole_0 @ X20 @ X18) != (k2_xboole_0 @ X19 @ X21))
% 0.24/0.57          | ~ (r1_xboole_0 @ X21 @ X18))),
% 0.24/0.57      inference('cnf', [status(esa)], [t72_xboole_1])).
% 0.24/0.57  thf('53', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.57         (((X0) != (k2_xboole_0 @ X2 @ X1))
% 0.24/0.57          | ~ (r1_xboole_0 @ X1 @ k1_xboole_0)
% 0.24/0.57          | ~ (r1_xboole_0 @ X2 @ X0)
% 0.24/0.57          | ((X2) = (k1_xboole_0)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.24/0.57  thf('54', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 0.24/0.57      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.24/0.57  thf('55', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.57         (((X0) != (k2_xboole_0 @ X2 @ X1))
% 0.24/0.57          | ~ (r1_xboole_0 @ X2 @ X0)
% 0.24/0.57          | ((X2) = (k1_xboole_0)))),
% 0.24/0.57      inference('demod', [status(thm)], ['53', '54'])).
% 0.24/0.57  thf('56', plain,
% 0.24/0.57      (![X1 : $i, X2 : $i]:
% 0.24/0.57         (((X2) = (k1_xboole_0))
% 0.24/0.57          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.24/0.57      inference('simplify', [status(thm)], ['55'])).
% 0.24/0.57  thf('57', plain,
% 0.24/0.57      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['50', '56'])).
% 0.24/0.57  thf('58', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.24/0.57      inference('sup-', [status(thm)], ['49', '57'])).
% 0.24/0.57  thf('59', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.24/0.57      inference('sup+', [status(thm)], ['21', '58'])).
% 0.24/0.57  thf(t22_subset_1, conjecture,
% 0.24/0.57    (![A:$i]:
% 0.24/0.57     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.24/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.57    (~( ![A:$i]:
% 0.24/0.57        ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )),
% 0.24/0.57    inference('cnf.neg', [status(esa)], [t22_subset_1])).
% 0.24/0.57  thf('60', plain,
% 0.24/0.57      (((k2_subset_1 @ sk_A) != (k3_subset_1 @ sk_A @ (k1_subset_1 @ sk_A)))),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.24/0.57  thf('61', plain, (![X44 : $i]: ((k1_subset_1 @ X44) = (k1_xboole_0))),
% 0.24/0.57      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.24/0.57  thf('62', plain,
% 0.24/0.57      (((k2_subset_1 @ sk_A) != (k3_subset_1 @ sk_A @ k1_xboole_0))),
% 0.24/0.57      inference('demod', [status(thm)], ['60', '61'])).
% 0.24/0.57  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.24/0.57  thf('63', plain, (![X45 : $i]: ((k2_subset_1 @ X45) = (X45))),
% 0.24/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.24/0.57  thf('64', plain, (((sk_A) != (k3_subset_1 @ sk_A @ k1_xboole_0))),
% 0.24/0.57      inference('demod', [status(thm)], ['62', '63'])).
% 0.24/0.57  thf('65', plain,
% 0.24/0.57      (![X0 : $i]: ((sk_A) != (k3_subset_1 @ sk_A @ (k3_subset_1 @ X0 @ X0)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['59', '64'])).
% 0.24/0.57  thf('66', plain, (((sk_A) != (sk_A))),
% 0.24/0.57      inference('sup-', [status(thm)], ['18', '65'])).
% 0.24/0.57  thf('67', plain, ($false), inference('simplify', [status(thm)], ['66'])).
% 0.24/0.57  
% 0.24/0.57  % SZS output end Refutation
% 0.24/0.57  
% 0.24/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
