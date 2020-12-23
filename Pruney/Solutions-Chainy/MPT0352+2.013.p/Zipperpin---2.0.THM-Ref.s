%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P1TZIbmuDb

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:09 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 557 expanded)
%              Number of leaves         :   27 ( 179 expanded)
%              Depth                    :   21
%              Number of atoms          :  798 (4682 expanded)
%              Number of equality atoms :   46 ( 285 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t31_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ C )
            <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X28: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('9',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( r1_tarski @ X21 @ X19 )
      | ( X20
       != ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('11',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_tarski @ X21 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['9','11'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['4','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('26',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X28: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('31',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_tarski @ X21 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('33',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('41',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['26','41'])).

thf('43',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','23','42'])).

thf('44',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['26','41'])).

thf('46',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['45','47'])).

thf('49',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['4','22'])).

thf('50',plain,
    ( ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('52',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) ) @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('60',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('64',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','64'])).

thf('66',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['44','67'])).

thf('69',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['43','68'])).

thf('70',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['46'])).

thf('71',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('72',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('76',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['46'])).

thf('78',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['44','67','77'])).

thf('79',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['76','78'])).

thf('80',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('81',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('83',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['69','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P1TZIbmuDb
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:10:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.17/1.36  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.17/1.36  % Solved by: fo/fo7.sh
% 1.17/1.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.17/1.36  % done 2208 iterations in 0.884s
% 1.17/1.36  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.17/1.36  % SZS output start Refutation
% 1.17/1.36  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.17/1.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.17/1.36  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.17/1.36  thf(sk_A_type, type, sk_A: $i).
% 1.17/1.36  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.17/1.36  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.17/1.36  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.17/1.36  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.17/1.36  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.17/1.36  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.17/1.36  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.17/1.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.17/1.36  thf(sk_B_type, type, sk_B: $i).
% 1.17/1.36  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.17/1.36  thf(t31_subset_1, conjecture,
% 1.17/1.36    (![A:$i,B:$i]:
% 1.17/1.36     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.17/1.36       ( ![C:$i]:
% 1.17/1.36         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.17/1.36           ( ( r1_tarski @ B @ C ) <=>
% 1.17/1.36             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 1.17/1.36  thf(zf_stmt_0, negated_conjecture,
% 1.17/1.36    (~( ![A:$i,B:$i]:
% 1.17/1.36        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.17/1.36          ( ![C:$i]:
% 1.17/1.36            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.17/1.36              ( ( r1_tarski @ B @ C ) <=>
% 1.17/1.36                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 1.17/1.36    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 1.17/1.36  thf('0', plain,
% 1.17/1.36      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.17/1.36           (k3_subset_1 @ sk_A @ sk_B))
% 1.17/1.36        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 1.17/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.36  thf('1', plain,
% 1.17/1.36      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.17/1.36           (k3_subset_1 @ sk_A @ sk_B)))
% 1.17/1.36         <= (~
% 1.17/1.36             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.17/1.36               (k3_subset_1 @ sk_A @ sk_B))))),
% 1.17/1.36      inference('split', [status(esa)], ['0'])).
% 1.17/1.36  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.17/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.36  thf(d5_subset_1, axiom,
% 1.17/1.36    (![A:$i,B:$i]:
% 1.17/1.36     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.17/1.36       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.17/1.36  thf('3', plain,
% 1.17/1.36      (![X26 : $i, X27 : $i]:
% 1.17/1.36         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 1.17/1.36          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 1.17/1.36      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.17/1.36  thf('4', plain,
% 1.17/1.36      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 1.17/1.36      inference('sup-', [status(thm)], ['2', '3'])).
% 1.17/1.36  thf('5', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.17/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.36  thf(d2_subset_1, axiom,
% 1.17/1.36    (![A:$i,B:$i]:
% 1.17/1.36     ( ( ( v1_xboole_0 @ A ) =>
% 1.17/1.36         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.17/1.36       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.17/1.36         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.17/1.36  thf('6', plain,
% 1.17/1.36      (![X23 : $i, X24 : $i]:
% 1.17/1.36         (~ (m1_subset_1 @ X23 @ X24)
% 1.17/1.36          | (r2_hidden @ X23 @ X24)
% 1.17/1.36          | (v1_xboole_0 @ X24))),
% 1.17/1.36      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.17/1.36  thf('7', plain,
% 1.17/1.36      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.17/1.36        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.17/1.36      inference('sup-', [status(thm)], ['5', '6'])).
% 1.17/1.36  thf(fc1_subset_1, axiom,
% 1.17/1.36    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.17/1.36  thf('8', plain, (![X28 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 1.17/1.36      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.17/1.36  thf('9', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.17/1.36      inference('clc', [status(thm)], ['7', '8'])).
% 1.17/1.36  thf(d1_zfmisc_1, axiom,
% 1.17/1.36    (![A:$i,B:$i]:
% 1.17/1.36     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.17/1.36       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.17/1.36  thf('10', plain,
% 1.17/1.36      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.17/1.36         (~ (r2_hidden @ X21 @ X20)
% 1.17/1.36          | (r1_tarski @ X21 @ X19)
% 1.17/1.36          | ((X20) != (k1_zfmisc_1 @ X19)))),
% 1.17/1.36      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.17/1.36  thf('11', plain,
% 1.17/1.36      (![X19 : $i, X21 : $i]:
% 1.17/1.36         ((r1_tarski @ X21 @ X19) | ~ (r2_hidden @ X21 @ (k1_zfmisc_1 @ X19)))),
% 1.17/1.36      inference('simplify', [status(thm)], ['10'])).
% 1.17/1.36  thf('12', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 1.17/1.36      inference('sup-', [status(thm)], ['9', '11'])).
% 1.17/1.36  thf(l32_xboole_1, axiom,
% 1.17/1.36    (![A:$i,B:$i]:
% 1.17/1.36     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.17/1.36  thf('13', plain,
% 1.17/1.36      (![X4 : $i, X6 : $i]:
% 1.17/1.36         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 1.17/1.36      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.17/1.36  thf('14', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 1.17/1.36      inference('sup-', [status(thm)], ['12', '13'])).
% 1.17/1.36  thf(t48_xboole_1, axiom,
% 1.17/1.36    (![A:$i,B:$i]:
% 1.17/1.36     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.17/1.36  thf('15', plain,
% 1.17/1.36      (![X16 : $i, X17 : $i]:
% 1.17/1.36         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.17/1.36           = (k3_xboole_0 @ X16 @ X17))),
% 1.17/1.36      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.17/1.36  thf('16', plain,
% 1.17/1.36      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 1.17/1.36      inference('sup+', [status(thm)], ['14', '15'])).
% 1.17/1.36  thf(t3_boole, axiom,
% 1.17/1.36    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.17/1.36  thf('17', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.17/1.36      inference('cnf', [status(esa)], [t3_boole])).
% 1.17/1.36  thf('18', plain, (((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 1.17/1.36      inference('demod', [status(thm)], ['16', '17'])).
% 1.17/1.36  thf(commutativity_k3_xboole_0, axiom,
% 1.17/1.36    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.17/1.36  thf('19', plain,
% 1.17/1.36      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.17/1.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.17/1.36  thf(t100_xboole_1, axiom,
% 1.17/1.36    (![A:$i,B:$i]:
% 1.17/1.36     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.17/1.36  thf('20', plain,
% 1.17/1.36      (![X7 : $i, X8 : $i]:
% 1.17/1.36         ((k4_xboole_0 @ X7 @ X8)
% 1.17/1.36           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 1.17/1.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.17/1.36  thf('21', plain,
% 1.17/1.36      (![X0 : $i, X1 : $i]:
% 1.17/1.36         ((k4_xboole_0 @ X0 @ X1)
% 1.17/1.36           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.17/1.36      inference('sup+', [status(thm)], ['19', '20'])).
% 1.17/1.36  thf('22', plain,
% 1.17/1.36      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 1.17/1.36      inference('sup+', [status(thm)], ['18', '21'])).
% 1.17/1.36  thf('23', plain,
% 1.17/1.36      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 1.17/1.36      inference('sup+', [status(thm)], ['4', '22'])).
% 1.17/1.36  thf('24', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.17/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.36  thf('25', plain,
% 1.17/1.36      (![X26 : $i, X27 : $i]:
% 1.17/1.36         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 1.17/1.36          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 1.17/1.36      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.17/1.36  thf('26', plain,
% 1.17/1.36      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.17/1.36      inference('sup-', [status(thm)], ['24', '25'])).
% 1.17/1.36  thf('27', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.17/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.36  thf('28', plain,
% 1.17/1.36      (![X23 : $i, X24 : $i]:
% 1.17/1.36         (~ (m1_subset_1 @ X23 @ X24)
% 1.17/1.36          | (r2_hidden @ X23 @ X24)
% 1.17/1.36          | (v1_xboole_0 @ X24))),
% 1.17/1.36      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.17/1.36  thf('29', plain,
% 1.17/1.36      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.17/1.36        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 1.17/1.36      inference('sup-', [status(thm)], ['27', '28'])).
% 1.17/1.36  thf('30', plain, (![X28 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 1.17/1.36      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.17/1.36  thf('31', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.17/1.36      inference('clc', [status(thm)], ['29', '30'])).
% 1.17/1.36  thf('32', plain,
% 1.17/1.36      (![X19 : $i, X21 : $i]:
% 1.17/1.36         ((r1_tarski @ X21 @ X19) | ~ (r2_hidden @ X21 @ (k1_zfmisc_1 @ X19)))),
% 1.17/1.36      inference('simplify', [status(thm)], ['10'])).
% 1.17/1.36  thf('33', plain, ((r1_tarski @ sk_B @ sk_A)),
% 1.17/1.36      inference('sup-', [status(thm)], ['31', '32'])).
% 1.17/1.36  thf('34', plain,
% 1.17/1.36      (![X4 : $i, X6 : $i]:
% 1.17/1.36         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 1.17/1.36      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.17/1.36  thf('35', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.17/1.36      inference('sup-', [status(thm)], ['33', '34'])).
% 1.17/1.36  thf('36', plain,
% 1.17/1.36      (![X16 : $i, X17 : $i]:
% 1.17/1.36         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.17/1.36           = (k3_xboole_0 @ X16 @ X17))),
% 1.17/1.36      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.17/1.36  thf('37', plain,
% 1.17/1.36      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.17/1.36      inference('sup+', [status(thm)], ['35', '36'])).
% 1.17/1.36  thf('38', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.17/1.36      inference('cnf', [status(esa)], [t3_boole])).
% 1.17/1.36  thf('39', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.17/1.36      inference('demod', [status(thm)], ['37', '38'])).
% 1.17/1.36  thf('40', plain,
% 1.17/1.36      (![X0 : $i, X1 : $i]:
% 1.17/1.36         ((k4_xboole_0 @ X0 @ X1)
% 1.17/1.36           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.17/1.36      inference('sup+', [status(thm)], ['19', '20'])).
% 1.17/1.36  thf('41', plain,
% 1.17/1.36      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 1.17/1.36      inference('sup+', [status(thm)], ['39', '40'])).
% 1.17/1.36  thf('42', plain,
% 1.17/1.36      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 1.17/1.36      inference('sup+', [status(thm)], ['26', '41'])).
% 1.17/1.36  thf('43', plain,
% 1.17/1.36      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 1.17/1.36           (k5_xboole_0 @ sk_A @ sk_B)))
% 1.17/1.36         <= (~
% 1.17/1.36             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.17/1.36               (k3_subset_1 @ sk_A @ sk_B))))),
% 1.17/1.36      inference('demod', [status(thm)], ['1', '23', '42'])).
% 1.17/1.36  thf('44', plain,
% 1.17/1.36      (~
% 1.17/1.36       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.17/1.36         (k3_subset_1 @ sk_A @ sk_B))) | 
% 1.17/1.36       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 1.17/1.36      inference('split', [status(esa)], ['0'])).
% 1.17/1.36  thf('45', plain,
% 1.17/1.36      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 1.17/1.36      inference('sup+', [status(thm)], ['26', '41'])).
% 1.17/1.36  thf('46', plain,
% 1.17/1.36      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.17/1.36         (k3_subset_1 @ sk_A @ sk_B))
% 1.17/1.36        | (r1_tarski @ sk_B @ sk_C_1))),
% 1.17/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.36  thf('47', plain,
% 1.17/1.36      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.17/1.36         (k3_subset_1 @ sk_A @ sk_B)))
% 1.17/1.36         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.17/1.36               (k3_subset_1 @ sk_A @ sk_B))))),
% 1.17/1.36      inference('split', [status(esa)], ['46'])).
% 1.17/1.36  thf('48', plain,
% 1.17/1.36      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.17/1.36         (k5_xboole_0 @ sk_A @ sk_B)))
% 1.17/1.36         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.17/1.36               (k3_subset_1 @ sk_A @ sk_B))))),
% 1.17/1.36      inference('sup+', [status(thm)], ['45', '47'])).
% 1.17/1.36  thf('49', plain,
% 1.17/1.36      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 1.17/1.36      inference('sup+', [status(thm)], ['4', '22'])).
% 1.17/1.36  thf('50', plain,
% 1.17/1.36      (((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 1.17/1.36         (k5_xboole_0 @ sk_A @ sk_B)))
% 1.17/1.36         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.17/1.36               (k3_subset_1 @ sk_A @ sk_B))))),
% 1.17/1.36      inference('demod', [status(thm)], ['48', '49'])).
% 1.17/1.36  thf('51', plain,
% 1.17/1.36      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 1.17/1.36      inference('sup+', [status(thm)], ['18', '21'])).
% 1.17/1.36  thf(t44_xboole_1, axiom,
% 1.17/1.36    (![A:$i,B:$i,C:$i]:
% 1.17/1.36     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.17/1.36       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.17/1.36  thf('52', plain,
% 1.17/1.36      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.17/1.36         ((r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 1.17/1.36          | ~ (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15))),
% 1.17/1.36      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.17/1.36  thf('53', plain,
% 1.17/1.36      (![X0 : $i]:
% 1.17/1.36         (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ X0)
% 1.17/1.36          | (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 1.17/1.36      inference('sup-', [status(thm)], ['51', '52'])).
% 1.17/1.36  thf('54', plain,
% 1.17/1.36      (((r1_tarski @ sk_A @ 
% 1.17/1.36         (k2_xboole_0 @ sk_C_1 @ (k5_xboole_0 @ sk_A @ sk_B))))
% 1.17/1.36         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.17/1.36               (k3_subset_1 @ sk_A @ sk_B))))),
% 1.17/1.36      inference('sup-', [status(thm)], ['50', '53'])).
% 1.17/1.36  thf(commutativity_k2_xboole_0, axiom,
% 1.17/1.36    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.17/1.36  thf('55', plain,
% 1.17/1.36      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.17/1.36      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.17/1.36  thf(t43_xboole_1, axiom,
% 1.17/1.36    (![A:$i,B:$i,C:$i]:
% 1.17/1.36     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.17/1.36       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.17/1.36  thf('56', plain,
% 1.17/1.36      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.17/1.36         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 1.17/1.36          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 1.17/1.36      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.17/1.36  thf('57', plain,
% 1.17/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.17/1.36         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 1.17/1.36          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 1.17/1.36      inference('sup-', [status(thm)], ['55', '56'])).
% 1.17/1.36  thf('58', plain,
% 1.17/1.36      (((r1_tarski @ (k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)) @ 
% 1.17/1.36         sk_C_1))
% 1.17/1.36         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.17/1.36               (k3_subset_1 @ sk_A @ sk_B))))),
% 1.17/1.36      inference('sup-', [status(thm)], ['54', '57'])).
% 1.17/1.36  thf('59', plain,
% 1.17/1.36      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 1.17/1.36      inference('sup+', [status(thm)], ['39', '40'])).
% 1.17/1.36  thf('60', plain,
% 1.17/1.36      (![X16 : $i, X17 : $i]:
% 1.17/1.36         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.17/1.36           = (k3_xboole_0 @ X16 @ X17))),
% 1.17/1.36      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.17/1.36  thf('61', plain,
% 1.17/1.36      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B))
% 1.17/1.36         = (k3_xboole_0 @ sk_A @ sk_B))),
% 1.17/1.36      inference('sup+', [status(thm)], ['59', '60'])).
% 1.17/1.36  thf('62', plain,
% 1.17/1.36      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.17/1.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.17/1.36  thf('63', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.17/1.36      inference('demod', [status(thm)], ['37', '38'])).
% 1.17/1.36  thf('64', plain,
% 1.17/1.36      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 1.17/1.36      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.17/1.36  thf('65', plain,
% 1.17/1.36      (((r1_tarski @ sk_B @ sk_C_1))
% 1.17/1.36         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.17/1.36               (k3_subset_1 @ sk_A @ sk_B))))),
% 1.17/1.36      inference('demod', [status(thm)], ['58', '64'])).
% 1.17/1.36  thf('66', plain,
% 1.17/1.36      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 1.17/1.36      inference('split', [status(esa)], ['0'])).
% 1.17/1.36  thf('67', plain,
% 1.17/1.36      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 1.17/1.36       ~
% 1.17/1.36       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.17/1.36         (k3_subset_1 @ sk_A @ sk_B)))),
% 1.17/1.36      inference('sup-', [status(thm)], ['65', '66'])).
% 1.17/1.36  thf('68', plain,
% 1.17/1.36      (~
% 1.17/1.36       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.17/1.36         (k3_subset_1 @ sk_A @ sk_B)))),
% 1.17/1.36      inference('sat_resolution*', [status(thm)], ['44', '67'])).
% 1.17/1.36  thf('69', plain,
% 1.17/1.36      (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 1.17/1.36          (k5_xboole_0 @ sk_A @ sk_B))),
% 1.17/1.36      inference('simpl_trail', [status(thm)], ['43', '68'])).
% 1.17/1.36  thf('70', plain,
% 1.17/1.36      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 1.17/1.36      inference('split', [status(esa)], ['46'])).
% 1.17/1.36  thf('71', plain,
% 1.17/1.36      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 1.17/1.36      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.17/1.36  thf('72', plain,
% 1.17/1.36      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.17/1.36         ((r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 1.17/1.36          | ~ (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15))),
% 1.17/1.36      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.17/1.36  thf('73', plain,
% 1.17/1.36      (![X0 : $i]:
% 1.17/1.36         (~ (r1_tarski @ sk_B @ X0)
% 1.17/1.36          | (r1_tarski @ sk_A @ 
% 1.17/1.36             (k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ X0)))),
% 1.17/1.36      inference('sup-', [status(thm)], ['71', '72'])).
% 1.17/1.36  thf('74', plain,
% 1.17/1.36      (((r1_tarski @ sk_A @ 
% 1.17/1.36         (k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_C_1)))
% 1.17/1.36         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 1.17/1.36      inference('sup-', [status(thm)], ['70', '73'])).
% 1.17/1.36  thf('75', plain,
% 1.17/1.36      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.17/1.36      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.17/1.36  thf('76', plain,
% 1.17/1.36      (((r1_tarski @ sk_A @ 
% 1.17/1.36         (k2_xboole_0 @ sk_C_1 @ (k5_xboole_0 @ sk_A @ sk_B))))
% 1.17/1.36         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 1.17/1.36      inference('demod', [status(thm)], ['74', '75'])).
% 1.17/1.36  thf('77', plain,
% 1.17/1.36      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 1.17/1.36       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 1.17/1.36         (k3_subset_1 @ sk_A @ sk_B)))),
% 1.17/1.36      inference('split', [status(esa)], ['46'])).
% 1.17/1.36  thf('78', plain, (((r1_tarski @ sk_B @ sk_C_1))),
% 1.17/1.36      inference('sat_resolution*', [status(thm)], ['44', '67', '77'])).
% 1.17/1.36  thf('79', plain,
% 1.17/1.36      ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C_1 @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 1.17/1.36      inference('simpl_trail', [status(thm)], ['76', '78'])).
% 1.17/1.36  thf('80', plain,
% 1.17/1.36      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.17/1.36         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 1.17/1.36          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 1.17/1.36      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.17/1.36  thf('81', plain,
% 1.17/1.36      ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ (k5_xboole_0 @ sk_A @ sk_B))),
% 1.17/1.36      inference('sup-', [status(thm)], ['79', '80'])).
% 1.17/1.36  thf('82', plain,
% 1.17/1.36      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 1.17/1.36      inference('sup+', [status(thm)], ['18', '21'])).
% 1.17/1.36  thf('83', plain,
% 1.17/1.36      ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ (k5_xboole_0 @ sk_A @ sk_B))),
% 1.17/1.36      inference('demod', [status(thm)], ['81', '82'])).
% 1.17/1.36  thf('84', plain, ($false), inference('demod', [status(thm)], ['69', '83'])).
% 1.17/1.36  
% 1.17/1.36  % SZS output end Refutation
% 1.17/1.36  
% 1.17/1.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
