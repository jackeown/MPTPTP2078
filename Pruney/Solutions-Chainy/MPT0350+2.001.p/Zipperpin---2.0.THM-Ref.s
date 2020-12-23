%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aV6thnxAcL

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 593 expanded)
%              Number of leaves         :   39 ( 200 expanded)
%              Depth                    :   19
%              Number of atoms          : 1120 (4378 expanded)
%              Number of equality atoms :  104 ( 374 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k3_subset_1 @ X45 @ X46 )
        = ( k4_xboole_0 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ X42 )
      | ( r2_hidden @ X41 @ X42 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X47: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('11',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X37 @ X36 )
      | ( r1_tarski @ X37 @ X35 )
      | ( X36
       != ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('13',plain,(
    ! [X35: $i,X37: $i] :
      ( ( r1_tarski @ X37 @ X35 )
      | ~ ( r2_hidden @ X37 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['11','13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['5','6','16'])).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('21',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('24',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf('28',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ X34 @ X35 )
      | ( r2_hidden @ X34 @ X36 )
      | ( X36
       != ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('32',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r2_hidden @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( r1_tarski @ X34 @ X35 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ( m1_subset_1 @ X41 @ X42 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X47: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('37',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('39',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X49 ) )
      | ( ( k4_subset_1 @ X49 @ X48 @ X50 )
        = ( k2_xboole_0 @ X48 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('44',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( X12 != X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('55',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r2_hidden @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( r1_tarski @ X34 @ X35 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ( m1_subset_1 @ X41 @ X42 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X47: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k3_subset_1 @ X45 @ X46 )
        = ( k4_xboole_0 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','62'])).

thf('64',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k3_subset_1 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['47','63'])).

thf('65',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('66',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_B @ sk_B ) )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('67',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_tarski @ X31 @ X30 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('68',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_B @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['66','71'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('73',plain,(
    ! [X19: $i] :
      ( r1_tarski @ k1_xboole_0 @ X19 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('74',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r2_hidden @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( r1_tarski @ X34 @ X35 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ( m1_subset_1 @ X41 @ X42 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X47: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k3_subset_1 @ X45 @ X46 )
        = ( k4_xboole_0 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X19: $i] :
      ( r1_tarski @ k1_xboole_0 @ X19 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('83',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('91',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['81','92'])).

thf('94',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('100',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['72','98','99'])).

thf('101',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','100'])).

thf('102',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('103',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X28 @ X29 ) @ ( k3_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('104',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('105',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k5_xboole_0 @ X29 @ ( k3_xboole_0 @ X28 @ X29 ) ) ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['102','105'])).

thf('107',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['5','6','16'])).

thf('108',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) )
      = ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('109',plain,
    ( ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('111',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('113',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['72','98','99'])).

thf('115',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_A )
    = ( k2_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','62'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('118',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('119',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['106','115','116','117','118'])).

thf('120',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['101','119'])).

thf('121',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['41','120'])).

thf('122',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('123',plain,(
    ! [X44: $i] :
      ( ( k2_subset_1 @ X44 )
      = X44 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('124',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['121','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aV6thnxAcL
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 269 iterations in 0.078s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(d3_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (![X3 : $i, X5 : $i]:
% 0.20/0.52         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf(t25_subset_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.20/0.52         ( k2_subset_1 @ A ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i]:
% 0.20/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.20/0.52            ( k2_subset_1 @ A ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.20/0.52  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d5_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X45 : $i, X46 : $i]:
% 0.20/0.52         (((k3_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))
% 0.20/0.52          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X45)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf(t48_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.20/0.52           = (k3_xboole_0 @ X22 @ X23))),
% 0.20/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.52         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.52  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d2_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.52       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X41 : $i, X42 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X41 @ X42)
% 0.20/0.52          | (r2_hidden @ X41 @ X42)
% 0.20/0.52          | (v1_xboole_0 @ X42))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.52        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf(fc1_subset_1, axiom,
% 0.20/0.52    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.52  thf('10', plain, (![X47 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X47))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.52  thf('11', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf(d1_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X37 @ X36)
% 0.20/0.52          | (r1_tarski @ X37 @ X35)
% 0.20/0.52          | ((X36) != (k1_zfmisc_1 @ X35)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X35 : $i, X37 : $i]:
% 0.20/0.52         ((r1_tarski @ X37 @ X35) | ~ (r2_hidden @ X37 @ (k1_zfmisc_1 @ X35)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.52  thf('14', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.52  thf(t28_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i]:
% 0.20/0.52         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.20/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.52  thf('16', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['5', '6', '16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.20/0.52           = (k3_xboole_0 @ X22 @ X23))),
% 0.20/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.20/0.52         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ sk_B)
% 0.20/0.52         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.52  thf(d4_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.52           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X10 @ X9)
% 0.20/0.52          | (r2_hidden @ X10 @ X8)
% 0.20/0.52          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.20/0.52         ((r2_hidden @ X10 @ X8)
% 0.20/0.52          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['22', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.52          | (r2_hidden @ X0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['21', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 0.20/0.52          | (r2_hidden @ (sk_C @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '26'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X3 : $i, X5 : $i]:
% 0.20/0.52         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.52        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf('30', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.52      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.52         (~ (r1_tarski @ X34 @ X35)
% 0.20/0.52          | (r2_hidden @ X34 @ X36)
% 0.20/0.52          | ((X36) != (k1_zfmisc_1 @ X35)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X34 : $i, X35 : $i]:
% 0.20/0.52         ((r2_hidden @ X34 @ (k1_zfmisc_1 @ X35)) | ~ (r1_tarski @ X34 @ X35))),
% 0.20/0.52      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['30', '32'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (![X41 : $i, X42 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X41 @ X42)
% 0.20/0.52          | (m1_subset_1 @ X41 @ X42)
% 0.20/0.52          | (v1_xboole_0 @ X42))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.52        | (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf('36', plain, (![X47 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X47))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('38', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k4_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49))
% 0.20/0.52          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X49))
% 0.20/0.52          | ((k4_subset_1 @ X49 @ X48 @ X50) = (k2_xboole_0 @ X48 @ X50)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.52         = (k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['37', '40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf(t39_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 0.20/0.52           = (k2_xboole_0 @ X20 @ X21))),
% 0.20/0.52      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.52         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.52  thf('45', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf(t100_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X15 @ X16)
% 0.20/0.52           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.20/0.52      inference('sup+', [status(thm)], ['45', '46'])).
% 0.20/0.52  thf(d10_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]: ((r1_tarski @ X12 @ X13) | ((X12) != (X13)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('49', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 0.20/0.52      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i]:
% 0.20/0.52         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.20/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.52  thf('51', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X15 @ X16)
% 0.20/0.52           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['51', '52'])).
% 0.20/0.52  thf('54', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 0.20/0.52      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (![X34 : $i, X35 : $i]:
% 0.20/0.52         ((r2_hidden @ X34 @ (k1_zfmisc_1 @ X35)) | ~ (r1_tarski @ X34 @ X35))),
% 0.20/0.52      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.52  thf('56', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      (![X41 : $i, X42 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X41 @ X42)
% 0.20/0.52          | (m1_subset_1 @ X41 @ X42)
% 0.20/0.52          | (v1_xboole_0 @ X42))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.20/0.52          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.52  thf('59', plain, (![X47 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X47))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.52  thf('60', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.52      inference('clc', [status(thm)], ['58', '59'])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      (![X45 : $i, X46 : $i]:
% 0.20/0.52         (((k3_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))
% 0.20/0.52          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X45)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.52  thf('63', plain,
% 0.20/0.52      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['53', '62'])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (((k4_xboole_0 @ sk_B @ sk_A) = (k3_subset_1 @ sk_B @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['47', '63'])).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 0.20/0.52           = (k2_xboole_0 @ X20 @ X21))),
% 0.20/0.52      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.52  thf('66', plain,
% 0.20/0.52      (((k2_xboole_0 @ sk_A @ (k3_subset_1 @ sk_B @ sk_B))
% 0.20/0.52         = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup+', [status(thm)], ['64', '65'])).
% 0.20/0.52  thf(commutativity_k2_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.52  thf('67', plain,
% 0.20/0.52      (![X30 : $i, X31 : $i]:
% 0.20/0.52         ((k2_tarski @ X31 @ X30) = (k2_tarski @ X30 @ X31))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.52  thf(l51_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('68', plain,
% 0.20/0.52      (![X39 : $i, X40 : $i]:
% 0.20/0.52         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 0.20/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['67', '68'])).
% 0.20/0.52  thf('70', plain,
% 0.20/0.52      (![X39 : $i, X40 : $i]:
% 0.20/0.52         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 0.20/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.52  thf('71', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['69', '70'])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      (((k2_xboole_0 @ sk_A @ (k3_subset_1 @ sk_B @ sk_B))
% 0.20/0.52         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['66', '71'])).
% 0.20/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.52  thf('73', plain, (![X19 : $i]: (r1_tarski @ k1_xboole_0 @ X19)),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.52  thf('74', plain,
% 0.20/0.52      (![X34 : $i, X35 : $i]:
% 0.20/0.52         ((r2_hidden @ X34 @ (k1_zfmisc_1 @ X35)) | ~ (r1_tarski @ X34 @ X35))),
% 0.20/0.52      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.52  thf('75', plain,
% 0.20/0.52      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.52  thf('76', plain,
% 0.20/0.52      (![X41 : $i, X42 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X41 @ X42)
% 0.20/0.52          | (m1_subset_1 @ X41 @ X42)
% 0.20/0.52          | (v1_xboole_0 @ X42))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.52  thf('77', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.20/0.52          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.52  thf('78', plain, (![X47 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X47))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.52  thf('79', plain,
% 0.20/0.52      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.52      inference('clc', [status(thm)], ['77', '78'])).
% 0.20/0.52  thf('80', plain,
% 0.20/0.52      (![X45 : $i, X46 : $i]:
% 0.20/0.52         (((k3_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))
% 0.20/0.52          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X45)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.52  thf('81', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.52  thf('82', plain, (![X19 : $i]: (r1_tarski @ k1_xboole_0 @ X19)),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.52  thf('83', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i]:
% 0.20/0.52         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.20/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.52  thf('84', plain,
% 0.20/0.52      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['82', '83'])).
% 0.20/0.52  thf('85', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.52  thf('86', plain,
% 0.20/0.52      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['84', '85'])).
% 0.20/0.52  thf('87', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X15 @ X16)
% 0.20/0.52           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.52  thf('88', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['86', '87'])).
% 0.20/0.52  thf('89', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.52  thf('90', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['88', '89'])).
% 0.20/0.52  thf(t5_boole, axiom,
% 0.20/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.52  thf('91', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 0.20/0.52      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.52  thf('92', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['90', '91'])).
% 0.20/0.52  thf('93', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['81', '92'])).
% 0.20/0.52  thf('94', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.20/0.52           = (k3_xboole_0 @ X22 @ X23))),
% 0.20/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.52  thf('95', plain,
% 0.20/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['93', '94'])).
% 0.20/0.52  thf('96', plain,
% 0.20/0.52      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.52  thf('97', plain,
% 0.20/0.52      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['84', '85'])).
% 0.20/0.52  thf('98', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.20/0.52  thf('99', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['69', '70'])).
% 0.20/0.52  thf('100', plain,
% 0.20/0.52      (((k2_xboole_0 @ k1_xboole_0 @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['72', '98', '99'])).
% 0.20/0.52  thf('101', plain,
% 0.20/0.52      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.52         = (k2_xboole_0 @ k1_xboole_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['44', '100'])).
% 0.20/0.52  thf('102', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ sk_B)
% 0.20/0.52         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf(t94_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k2_xboole_0 @ A @ B ) =
% 0.20/0.52       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.52  thf('103', plain,
% 0.20/0.52      (![X28 : $i, X29 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ X28 @ X29)
% 0.20/0.52           = (k5_xboole_0 @ (k5_xboole_0 @ X28 @ X29) @ 
% 0.20/0.52              (k3_xboole_0 @ X28 @ X29)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.20/0.52  thf(t91_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.52       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.20/0.52  thf('104', plain,
% 0.20/0.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.52         ((k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ X27)
% 0.20/0.52           = (k5_xboole_0 @ X25 @ (k5_xboole_0 @ X26 @ X27)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.52  thf('105', plain,
% 0.20/0.52      (![X28 : $i, X29 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ X28 @ X29)
% 0.20/0.52           = (k5_xboole_0 @ X28 @ 
% 0.20/0.52              (k5_xboole_0 @ X29 @ (k3_xboole_0 @ X28 @ X29))))),
% 0.20/0.52      inference('demod', [status(thm)], ['103', '104'])).
% 0.20/0.52  thf('106', plain,
% 0.20/0.52      (((k2_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.52         = (k5_xboole_0 @ sk_A @ 
% 0.20/0.52            (k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.20/0.52             (k3_subset_1 @ sk_A @ sk_B))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['102', '105'])).
% 0.20/0.52  thf('107', plain,
% 0.20/0.52      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['5', '6', '16'])).
% 0.20/0.52  thf('108', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20))
% 0.20/0.52           = (k2_xboole_0 @ X20 @ X21))),
% 0.20/0.52      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.52  thf('109', plain,
% 0.20/0.52      (((k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.52         = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.52      inference('sup+', [status(thm)], ['107', '108'])).
% 0.20/0.52  thf('110', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['69', '70'])).
% 0.20/0.52  thf('111', plain,
% 0.20/0.52      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.52         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.52  thf('112', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['69', '70'])).
% 0.20/0.52  thf('113', plain,
% 0.20/0.52      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.20/0.52         = (k2_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 0.20/0.52  thf('114', plain,
% 0.20/0.52      (((k2_xboole_0 @ k1_xboole_0 @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['72', '98', '99'])).
% 0.20/0.52  thf('115', plain,
% 0.20/0.52      (((k2_xboole_0 @ k1_xboole_0 @ sk_A)
% 0.20/0.52         = (k2_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['113', '114'])).
% 0.20/0.52  thf('116', plain,
% 0.20/0.52      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['53', '62'])).
% 0.20/0.52  thf('117', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.20/0.52  thf('118', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 0.20/0.52      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.52  thf('119', plain, (((k2_xboole_0 @ k1_xboole_0 @ sk_A) = (sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['106', '115', '116', '117', '118'])).
% 0.20/0.52  thf('120', plain,
% 0.20/0.52      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['101', '119'])).
% 0.20/0.52  thf('121', plain,
% 0.20/0.52      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['41', '120'])).
% 0.20/0.52  thf('122', plain,
% 0.20/0.52      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.52         != (k2_subset_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.52  thf('123', plain, (![X44 : $i]: ((k2_subset_1 @ X44) = (X44))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.52  thf('124', plain,
% 0.20/0.52      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['122', '123'])).
% 0.20/0.52  thf('125', plain, ($false),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['121', '124'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
