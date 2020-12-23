%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dNIZiO6LgG

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:26 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 325 expanded)
%              Number of leaves         :   28 ( 103 expanded)
%              Depth                    :   17
%              Number of atoms          :  759 (2532 expanded)
%              Number of equality atoms :   72 ( 251 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X38: $i] :
      ( ( k1_subset_1 @ X38 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('3',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ( X15 != X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X16: $i] :
      ( r1_tarski @ X16 @ X16 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X24: $i,X26: $i] :
      ( ( r1_xboole_0 @ X24 @ X26 )
      | ( ( k4_xboole_0 @ X24 @ X26 )
       != X24 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('20',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('28',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf('32',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 )
      | ( ( k5_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 )
      | ( ( k5_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('37',plain,(
    ! [X16: $i] :
      ( r1_tarski @ X16 @ X16 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('38',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ( r1_xboole_0 @ X27 @ ( k4_xboole_0 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','41'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('43',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    ! [X38: $i] :
      ( ( k1_subset_1 @ X38 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('51',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','52'])).

thf('54',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','52'])).

thf('57',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','57'])).

thf('59',plain,(
    sk_B_1
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','58'])).

thf('60',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['3','59'])).

thf('61',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('62',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['51'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('67',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ~ ( r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('70',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k3_subset_1 @ X39 @ X40 )
        = ( k4_xboole_0 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('71',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('73',plain,(
    r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['68','73'])).

thf('75',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['51'])).

thf('76',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['4','58','75'])).

thf('77',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['74','76'])).

thf('78',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['60','77'])).

thf('79',plain,(
    $false ),
    inference(simplify,[status(thm)],['78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dNIZiO6LgG
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:28:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 238 iterations in 0.160s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.60  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.40/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.60  thf(t38_subset_1, conjecture,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.60       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.40/0.60         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i,B:$i]:
% 0.40/0.60        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.60          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.40/0.60            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.40/0.60  thf('0', plain,
% 0.40/0.60      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.40/0.60        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('1', plain,
% 0.40/0.60      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.40/0.60         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.40/0.60      inference('split', [status(esa)], ['0'])).
% 0.40/0.60  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.40/0.60  thf('2', plain, (![X38 : $i]: ((k1_subset_1 @ X38) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.40/0.60  thf('3', plain,
% 0.40/0.60      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['1', '2'])).
% 0.40/0.60  thf('4', plain,
% 0.40/0.60      (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) | 
% 0.40/0.60       ~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.40/0.60      inference('split', [status(esa)], ['0'])).
% 0.40/0.60  thf(d10_xboole_0, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.60  thf('5', plain,
% 0.40/0.60      (![X15 : $i, X16 : $i]: ((r1_tarski @ X15 @ X16) | ((X15) != (X16)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.60  thf('6', plain, (![X16 : $i]: (r1_tarski @ X16 @ X16)),
% 0.40/0.60      inference('simplify', [status(thm)], ['5'])).
% 0.40/0.60  thf(t28_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.60  thf('7', plain,
% 0.40/0.60      (![X20 : $i, X21 : $i]:
% 0.40/0.60         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.40/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.60  thf('8', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.60  thf(t100_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.60  thf('9', plain,
% 0.40/0.60      (![X18 : $i, X19 : $i]:
% 0.40/0.60         ((k4_xboole_0 @ X18 @ X19)
% 0.40/0.60           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.60  thf('10', plain,
% 0.40/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['8', '9'])).
% 0.40/0.60  thf(t48_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.60  thf('11', plain,
% 0.40/0.60      (![X22 : $i, X23 : $i]:
% 0.40/0.60         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.40/0.60           = (k3_xboole_0 @ X22 @ X23))),
% 0.40/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.60  thf('12', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.40/0.60           = (k3_xboole_0 @ X0 @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['10', '11'])).
% 0.40/0.60  thf('13', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.60  thf('14', plain,
% 0.40/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 0.40/0.60      inference('demod', [status(thm)], ['12', '13'])).
% 0.40/0.60  thf(t83_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.60  thf('15', plain,
% 0.40/0.60      (![X24 : $i, X26 : $i]:
% 0.40/0.60         ((r1_xboole_0 @ X24 @ X26) | ((k4_xboole_0 @ X24 @ X26) != (X24)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((X0) != (X0)) | (r1_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.60  thf('17', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.60      inference('simplify', [status(thm)], ['16'])).
% 0.40/0.60  thf(t7_xboole_0, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.40/0.60          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.40/0.60  thf('18', plain,
% 0.40/0.60      (![X14 : $i]:
% 0.40/0.60         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.40/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.40/0.60  thf('19', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.60  thf('20', plain,
% 0.40/0.60      (![X22 : $i, X23 : $i]:
% 0.40/0.60         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.40/0.60           = (k3_xboole_0 @ X22 @ X23))),
% 0.40/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.60  thf('21', plain,
% 0.40/0.60      (![X22 : $i, X23 : $i]:
% 0.40/0.60         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.40/0.60           = (k3_xboole_0 @ X22 @ X23))),
% 0.40/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.60  thf('22', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.40/0.60           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['20', '21'])).
% 0.40/0.60  thf('23', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((k4_xboole_0 @ X0 @ X0)
% 0.40/0.60           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['19', '22'])).
% 0.40/0.60  thf('24', plain,
% 0.40/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['8', '9'])).
% 0.40/0.60  thf('25', plain,
% 0.40/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['8', '9'])).
% 0.40/0.60  thf('26', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((k5_xboole_0 @ X0 @ X0)
% 0.40/0.60           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.40/0.60      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.40/0.60  thf(d4_xboole_0, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.40/0.60       ( ![D:$i]:
% 0.40/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.60           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.40/0.60  thf('27', plain,
% 0.40/0.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X8 @ X7)
% 0.40/0.60          | (r2_hidden @ X8 @ X5)
% 0.40/0.60          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.40/0.60  thf('28', plain,
% 0.40/0.60      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.40/0.60         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['27'])).
% 0.40/0.60  thf('29', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['26', '28'])).
% 0.40/0.60  thf('30', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.40/0.60          | (r2_hidden @ (sk_B @ (k5_xboole_0 @ X0 @ X0)) @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['18', '29'])).
% 0.40/0.60  thf('31', plain,
% 0.40/0.60      (![X14 : $i]:
% 0.40/0.60         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.40/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.40/0.60  thf(t3_xboole_0, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.40/0.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.60            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.40/0.60  thf('32', plain,
% 0.40/0.60      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X12 @ X10)
% 0.40/0.60          | ~ (r2_hidden @ X12 @ X13)
% 0.40/0.60          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.40/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.60  thf('33', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((X0) = (k1_xboole_0))
% 0.40/0.60          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.40/0.60          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.60  thf('34', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.40/0.60          | ~ (r1_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0)
% 0.40/0.60          | ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['30', '33'])).
% 0.40/0.60  thf('35', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (r1_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0)
% 0.40/0.60          | ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['34'])).
% 0.40/0.60  thf('36', plain,
% 0.40/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 0.40/0.60      inference('demod', [status(thm)], ['12', '13'])).
% 0.40/0.60  thf('37', plain, (![X16 : $i]: (r1_tarski @ X16 @ X16)),
% 0.40/0.60      inference('simplify', [status(thm)], ['5'])).
% 0.40/0.60  thf(t85_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.40/0.60  thf('38', plain,
% 0.40/0.60      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.40/0.60         (~ (r1_tarski @ X27 @ X28)
% 0.40/0.60          | (r1_xboole_0 @ X27 @ (k4_xboole_0 @ X29 @ X28)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.40/0.60  thf('39', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.40/0.60  thf('40', plain, (![X0 : $i]: (r1_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0)),
% 0.40/0.60      inference('sup+', [status(thm)], ['36', '39'])).
% 0.40/0.60  thf('41', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.60      inference('demod', [status(thm)], ['35', '40'])).
% 0.40/0.60  thf('42', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.40/0.60      inference('demod', [status(thm)], ['17', '41'])).
% 0.40/0.60  thf(d3_tarski, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.60  thf('43', plain,
% 0.40/0.60      (![X1 : $i, X3 : $i]:
% 0.40/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.60  thf('44', plain,
% 0.40/0.60      (![X1 : $i, X3 : $i]:
% 0.40/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.60  thf('45', plain,
% 0.40/0.60      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X12 @ X10)
% 0.40/0.60          | ~ (r2_hidden @ X12 @ X13)
% 0.40/0.60          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.40/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.60  thf('46', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         ((r1_tarski @ X0 @ X1)
% 0.40/0.60          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.40/0.60          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.40/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.40/0.60  thf('47', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r1_tarski @ X0 @ X1)
% 0.40/0.60          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.40/0.60          | (r1_tarski @ X0 @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['43', '46'])).
% 0.40/0.60  thf('48', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (r1_tarski @ X0 @ X1))),
% 0.40/0.60      inference('simplify', [status(thm)], ['47'])).
% 0.40/0.60  thf('49', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.40/0.60      inference('sup-', [status(thm)], ['42', '48'])).
% 0.40/0.60  thf('50', plain, (![X38 : $i]: ((k1_subset_1 @ X38) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.40/0.60  thf('51', plain,
% 0.40/0.60      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.40/0.60        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('52', plain,
% 0.40/0.60      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.40/0.60         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.40/0.60      inference('split', [status(esa)], ['51'])).
% 0.40/0.60  thf('53', plain,
% 0.40/0.60      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['50', '52'])).
% 0.40/0.60  thf('54', plain,
% 0.40/0.60      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.40/0.60         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.40/0.60      inference('split', [status(esa)], ['0'])).
% 0.40/0.60  thf('55', plain,
% 0.40/0.60      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.40/0.60         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.40/0.60             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['53', '54'])).
% 0.40/0.60  thf('56', plain,
% 0.40/0.60      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['50', '52'])).
% 0.40/0.60  thf('57', plain,
% 0.40/0.60      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.40/0.60         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.40/0.60             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.40/0.60      inference('demod', [status(thm)], ['55', '56'])).
% 0.40/0.60  thf('58', plain,
% 0.40/0.60      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.40/0.60       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['49', '57'])).
% 0.40/0.60  thf('59', plain, (~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.40/0.60      inference('sat_resolution*', [status(thm)], ['4', '58'])).
% 0.40/0.60  thf('60', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.40/0.60      inference('simpl_trail', [status(thm)], ['3', '59'])).
% 0.40/0.60  thf('61', plain,
% 0.40/0.60      (![X14 : $i]:
% 0.40/0.60         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.40/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.40/0.60  thf('62', plain,
% 0.40/0.60      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.40/0.60         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.40/0.60      inference('split', [status(esa)], ['51'])).
% 0.40/0.60  thf('63', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.60          | (r2_hidden @ X0 @ X2)
% 0.40/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.60  thf('64', plain,
% 0.40/0.60      ((![X0 : $i]:
% 0.40/0.60          ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.40/0.60           | ~ (r2_hidden @ X0 @ sk_B_1)))
% 0.40/0.60         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['62', '63'])).
% 0.40/0.60  thf('65', plain,
% 0.40/0.60      (((((sk_B_1) = (k1_xboole_0))
% 0.40/0.60         | (r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))))
% 0.40/0.60         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['61', '64'])).
% 0.40/0.60  thf('66', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((X0) = (k1_xboole_0))
% 0.40/0.60          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.40/0.60          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.60  thf('67', plain,
% 0.40/0.60      (((((sk_B_1) = (k1_xboole_0))
% 0.40/0.60         | ~ (r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.40/0.60         | ((sk_B_1) = (k1_xboole_0))))
% 0.40/0.60         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['65', '66'])).
% 0.40/0.60  thf('68', plain,
% 0.40/0.60      (((~ (r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.40/0.60         | ((sk_B_1) = (k1_xboole_0))))
% 0.40/0.60         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.40/0.60      inference('simplify', [status(thm)], ['67'])).
% 0.40/0.60  thf('69', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(d5_subset_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.60       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.40/0.60  thf('70', plain,
% 0.40/0.60      (![X39 : $i, X40 : $i]:
% 0.40/0.60         (((k3_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))
% 0.40/0.60          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.40/0.60  thf('71', plain,
% 0.40/0.60      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['69', '70'])).
% 0.40/0.60  thf('72', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.40/0.60  thf('73', plain, ((r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.40/0.60      inference('sup+', [status(thm)], ['71', '72'])).
% 0.40/0.60  thf('74', plain,
% 0.40/0.60      ((((sk_B_1) = (k1_xboole_0)))
% 0.40/0.60         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.40/0.60      inference('demod', [status(thm)], ['68', '73'])).
% 0.40/0.60  thf('75', plain,
% 0.40/0.60      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.40/0.60       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.40/0.60      inference('split', [status(esa)], ['51'])).
% 0.40/0.60  thf('76', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.40/0.60      inference('sat_resolution*', [status(thm)], ['4', '58', '75'])).
% 0.40/0.60  thf('77', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.40/0.60      inference('simpl_trail', [status(thm)], ['74', '76'])).
% 0.40/0.60  thf('78', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.40/0.60      inference('demod', [status(thm)], ['60', '77'])).
% 0.40/0.60  thf('79', plain, ($false), inference('simplify', [status(thm)], ['78'])).
% 0.40/0.60  
% 0.40/0.60  % SZS output end Refutation
% 0.40/0.60  
% 0.40/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
