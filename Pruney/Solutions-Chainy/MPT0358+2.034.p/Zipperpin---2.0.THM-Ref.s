%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KYlZ7T5dJU

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:26 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 269 expanded)
%              Number of leaves         :   23 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :  678 (2183 expanded)
%              Number of equality atoms :   56 ( 193 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('0',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ~ ( r1_tarski @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) )
      | ( sk_B
        = ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('11',plain,
    ( ( ~ ( r1_tarski @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) )
      | ( sk_B
        = ( k5_xboole_0 @ sk_B @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X31: $i] :
      ( ( k1_subset_1 @ X31 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('24',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['12'])).

thf('27',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('29',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['13','30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) )
    | ( sk_B
      = ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['11','32'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['34','50'])).

thf('52',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('55',plain,
    ( ~ ( r1_tarski @ sk_B @ k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','53','54'])).

thf('56',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('57',plain,(
    ! [X31: $i] :
      ( ( k1_subset_1 @ X31 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('58',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    sk_B
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['13','30'])).

thf('60',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( r1_tarski @ sk_B @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('64',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k4_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('65',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['13','30','31'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(clc,[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['62','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['61','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KYlZ7T5dJU
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 253 iterations in 0.085s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.35/0.53  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.35/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(t38_subset_1, conjecture,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.53       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.35/0.53         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i,B:$i]:
% 0.35/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.53          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.35/0.53            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.35/0.53  thf('0', plain,
% 0.35/0.53      ((((sk_B) = (k1_subset_1 @ sk_A))
% 0.35/0.53        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.35/0.53         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.35/0.53      inference('split', [status(esa)], ['0'])).
% 0.35/0.53  thf(t28_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      (![X18 : $i, X19 : $i]:
% 0.35/0.53         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.35/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.35/0.53  thf('3', plain,
% 0.35/0.53      ((((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.35/0.53         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.53  thf(t100_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      (![X13 : $i, X14 : $i]:
% 0.35/0.53         ((k4_xboole_0 @ X13 @ X14)
% 0.35/0.53           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.53  thf('5', plain,
% 0.35/0.53      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.35/0.53          = (k5_xboole_0 @ sk_B @ sk_B)))
% 0.35/0.53         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.35/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.35/0.53  thf(t36_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 0.35/0.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.35/0.53  thf(d10_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      (![X10 : $i, X12 : $i]:
% 0.35/0.53         (((X10) = (X12))
% 0.35/0.53          | ~ (r1_tarski @ X12 @ X10)
% 0.35/0.53          | ~ (r1_tarski @ X10 @ X12))),
% 0.35/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.53  thf('8', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.35/0.53          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.53  thf('9', plain,
% 0.35/0.53      (((~ (r1_tarski @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B))
% 0.35/0.53         | ((sk_B) = (k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))))
% 0.35/0.53         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['5', '8'])).
% 0.35/0.53  thf('10', plain,
% 0.35/0.53      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.35/0.53          = (k5_xboole_0 @ sk_B @ sk_B)))
% 0.35/0.53         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.35/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.35/0.53  thf('11', plain,
% 0.35/0.53      (((~ (r1_tarski @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B))
% 0.35/0.53         | ((sk_B) = (k5_xboole_0 @ sk_B @ sk_B))))
% 0.35/0.53         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.35/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.35/0.53  thf('12', plain,
% 0.35/0.53      ((((sk_B) != (k1_subset_1 @ sk_A))
% 0.35/0.53        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      (~ (((sk_B) = (k1_subset_1 @ sk_A))) | 
% 0.35/0.53       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.35/0.53      inference('split', [status(esa)], ['12'])).
% 0.35/0.53  thf(d3_tarski, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.35/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.35/0.53  thf('14', plain,
% 0.35/0.53      (![X1 : $i, X3 : $i]:
% 0.35/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 0.35/0.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.35/0.53  thf(t3_xboole_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.35/0.53  thf('16', plain,
% 0.35/0.53      (![X22 : $i]:
% 0.35/0.53         (((X22) = (k1_xboole_0)) | ~ (r1_tarski @ X22 @ k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.35/0.53  thf(d5_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.35/0.53       ( ![D:$i]:
% 0.35/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.53           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X8 @ X7)
% 0.35/0.53          | ~ (r2_hidden @ X8 @ X6)
% 0.35/0.53          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.35/0.53  thf('19', plain,
% 0.35/0.53      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X8 @ X6)
% 0.35/0.53          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.35/0.53  thf('20', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['17', '19'])).
% 0.35/0.53  thf('21', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.35/0.53      inference('condensation', [status(thm)], ['20'])).
% 0.35/0.53  thf('22', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.35/0.53      inference('sup-', [status(thm)], ['14', '21'])).
% 0.35/0.53  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.35/0.53  thf('23', plain, (![X31 : $i]: ((k1_subset_1 @ X31) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      ((((sk_B) = (k1_subset_1 @ sk_A))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.35/0.53      inference('split', [status(esa)], ['0'])).
% 0.35/0.53  thf('25', plain,
% 0.35/0.53      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.35/0.53      inference('sup+', [status(thm)], ['23', '24'])).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.35/0.53         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.35/0.53      inference('split', [status(esa)], ['12'])).
% 0.35/0.53  thf('27', plain,
% 0.35/0.53      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.35/0.53         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.35/0.53             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.53  thf('28', plain,
% 0.35/0.53      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.35/0.53      inference('sup+', [status(thm)], ['23', '24'])).
% 0.35/0.53  thf('29', plain,
% 0.35/0.53      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.35/0.53         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.35/0.53             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.35/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.35/0.53  thf('30', plain,
% 0.35/0.53      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.35/0.53       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['22', '29'])).
% 0.35/0.53  thf('31', plain,
% 0.35/0.53      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.35/0.53       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.35/0.53      inference('split', [status(esa)], ['0'])).
% 0.35/0.53  thf('32', plain, (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.35/0.53      inference('sat_resolution*', [status(thm)], ['13', '30', '31'])).
% 0.35/0.53  thf('33', plain,
% 0.35/0.53      ((~ (r1_tarski @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B))
% 0.35/0.53        | ((sk_B) = (k5_xboole_0 @ sk_B @ sk_B)))),
% 0.35/0.53      inference('simpl_trail', [status(thm)], ['11', '32'])).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      (![X1 : $i, X3 : $i]:
% 0.35/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.53  thf('35', plain,
% 0.35/0.53      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.53  thf('36', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.35/0.53      inference('simplify', [status(thm)], ['35'])).
% 0.35/0.53  thf('37', plain,
% 0.35/0.53      (![X18 : $i, X19 : $i]:
% 0.35/0.53         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.35/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.35/0.53  thf('38', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.35/0.53  thf('39', plain,
% 0.35/0.53      (![X13 : $i, X14 : $i]:
% 0.35/0.53         ((k4_xboole_0 @ X13 @ X14)
% 0.35/0.53           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.53  thf('40', plain,
% 0.35/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['38', '39'])).
% 0.35/0.53  thf('41', plain,
% 0.35/0.53      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 0.35/0.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.35/0.53  thf('42', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.35/0.53          | (r2_hidden @ X0 @ X2)
% 0.35/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.53  thf('43', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.53         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['41', '42'])).
% 0.35/0.53  thf('44', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['40', '43'])).
% 0.35/0.53  thf('45', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.35/0.53  thf('46', plain,
% 0.35/0.53      (![X13 : $i, X14 : $i]:
% 0.35/0.53         ((k4_xboole_0 @ X13 @ X14)
% 0.35/0.53           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.53  thf('47', plain,
% 0.35/0.53      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X8 @ X6)
% 0.35/0.53          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.35/0.53  thf('48', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.35/0.53          | ~ (r2_hidden @ X2 @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.35/0.53  thf('49', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.35/0.53          | ~ (r2_hidden @ X1 @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['45', '48'])).
% 0.35/0.53  thf('50', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.35/0.53      inference('clc', [status(thm)], ['44', '49'])).
% 0.35/0.53  thf('51', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 0.35/0.53      inference('sup-', [status(thm)], ['34', '50'])).
% 0.35/0.53  thf('52', plain,
% 0.35/0.53      (![X22 : $i]:
% 0.35/0.53         (((X22) = (k1_xboole_0)) | ~ (r1_tarski @ X22 @ k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.35/0.53  thf('53', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.35/0.53  thf('54', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.35/0.53  thf('55', plain,
% 0.35/0.53      ((~ (r1_tarski @ sk_B @ k1_xboole_0) | ((sk_B) = (k1_xboole_0)))),
% 0.35/0.53      inference('demod', [status(thm)], ['33', '53', '54'])).
% 0.35/0.53  thf('56', plain,
% 0.35/0.53      ((((sk_B) != (k1_subset_1 @ sk_A)))
% 0.35/0.53         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.35/0.53      inference('split', [status(esa)], ['12'])).
% 0.35/0.53  thf('57', plain, (![X31 : $i]: ((k1_subset_1 @ X31) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.35/0.53  thf('58', plain,
% 0.35/0.53      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.35/0.53      inference('demod', [status(thm)], ['56', '57'])).
% 0.35/0.53  thf('59', plain, (~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.35/0.53      inference('sat_resolution*', [status(thm)], ['13', '30'])).
% 0.35/0.53  thf('60', plain, (((sk_B) != (k1_xboole_0))),
% 0.35/0.53      inference('simpl_trail', [status(thm)], ['58', '59'])).
% 0.35/0.53  thf('61', plain, (~ (r1_tarski @ sk_B @ k1_xboole_0)),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['55', '60'])).
% 0.35/0.53  thf('62', plain,
% 0.35/0.53      (![X1 : $i, X3 : $i]:
% 0.35/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.53  thf('63', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(d5_subset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.35/0.53  thf('64', plain,
% 0.35/0.53      (![X32 : $i, X33 : $i]:
% 0.35/0.53         (((k3_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))
% 0.35/0.53          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.35/0.53  thf('65', plain,
% 0.35/0.53      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['63', '64'])).
% 0.35/0.53  thf('66', plain,
% 0.35/0.53      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X8 @ X6)
% 0.35/0.53          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.35/0.53  thf('67', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.35/0.53          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['65', '66'])).
% 0.35/0.53  thf('68', plain,
% 0.35/0.53      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.35/0.53         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.35/0.53      inference('split', [status(esa)], ['0'])).
% 0.35/0.53  thf('69', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.35/0.53          | (r2_hidden @ X0 @ X2)
% 0.35/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.53  thf('70', plain,
% 0.38/0.53      ((![X0 : $i]:
% 0.38/0.53          ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.38/0.53           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.38/0.53         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.38/0.53      inference('sup-', [status(thm)], ['68', '69'])).
% 0.38/0.53  thf('71', plain, (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.38/0.53      inference('sat_resolution*', [status(thm)], ['13', '30', '31'])).
% 0.38/0.53  thf('72', plain,
% 0.38/0.53      (![X0 : $i]:
% 0.38/0.53         ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.38/0.53          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.38/0.53      inference('simpl_trail', [status(thm)], ['70', '71'])).
% 0.38/0.53  thf('73', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.38/0.53      inference('clc', [status(thm)], ['67', '72'])).
% 0.38/0.53  thf('74', plain, (![X0 : $i]: (r1_tarski @ sk_B @ X0)),
% 0.38/0.53      inference('sup-', [status(thm)], ['62', '73'])).
% 0.38/0.53  thf('75', plain, ($false), inference('demod', [status(thm)], ['61', '74'])).
% 0.38/0.53  
% 0.38/0.53  % SZS output end Refutation
% 0.38/0.53  
% 0.38/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
