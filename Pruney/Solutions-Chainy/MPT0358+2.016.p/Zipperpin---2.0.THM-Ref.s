%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mjf1U07Wc0

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:24 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 336 expanded)
%              Number of leaves         :   28 ( 108 expanded)
%              Depth                    :   20
%              Number of atoms          :  687 (2625 expanded)
%              Number of equality atoms :   61 ( 216 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('2',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('24',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['8','26'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('32',plain,(
    ! [X27: $i] :
      ( ( k1_subset_1 @ X27 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('33',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('34',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['6'])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('38',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['8','26'])).

thf('41',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('43',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['7','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['5','43'])).

thf('45',plain,(
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

thf('46',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ X25 )
      | ( r2_hidden @ X24 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('48',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('49',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('50',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( r1_tarski @ X22 @ X20 )
      | ( X21
       != ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('51',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_tarski @ X22 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('60',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('61',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','62'])).

thf('64',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('65',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(clc,[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['1','67'])).

thf('69',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup+',[status(thm)],['0','70'])).

thf('72',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf('73',plain,(
    ! [X27: $i] :
      ( ( k1_subset_1 @ X27 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('74',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    sk_B
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['7','41'])).

thf('76',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['71','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mjf1U07Wc0
% 0.11/0.32  % Computer   : n004.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 19:07:39 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.18/0.33  % Python version: Python 3.6.8
% 0.18/0.33  % Running in FO mode
% 0.19/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.55  % Solved by: fo/fo7.sh
% 0.19/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.55  % done 197 iterations in 0.108s
% 0.19/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.55  % SZS output start Refutation
% 0.19/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.55  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.19/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.55  thf(t1_boole, axiom,
% 0.19/0.55    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.55  thf('0', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.19/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.19/0.55  thf(d3_tarski, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.55  thf('1', plain,
% 0.19/0.55      (![X3 : $i, X5 : $i]:
% 0.19/0.55         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.55  thf(t38_subset_1, conjecture,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.55       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.19/0.55         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.19/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.55    (~( ![A:$i,B:$i]:
% 0.19/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.55          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.19/0.55            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.19/0.55    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.19/0.55  thf('2', plain,
% 0.19/0.55      ((((sk_B) = (k1_subset_1 @ sk_A))
% 0.19/0.55        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('3', plain,
% 0.19/0.55      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.19/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.19/0.55      inference('split', [status(esa)], ['2'])).
% 0.19/0.55  thf('4', plain,
% 0.19/0.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X2 @ X3)
% 0.19/0.55          | (r2_hidden @ X2 @ X4)
% 0.19/0.55          | ~ (r1_tarski @ X3 @ X4))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.55  thf('5', plain,
% 0.19/0.55      ((![X0 : $i]:
% 0.19/0.55          ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.55           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.19/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.55  thf('6', plain,
% 0.19/0.55      ((((sk_B) != (k1_subset_1 @ sk_A))
% 0.19/0.55        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('7', plain,
% 0.19/0.55      (~ (((sk_B) = (k1_subset_1 @ sk_A))) | 
% 0.19/0.55       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.55      inference('split', [status(esa)], ['6'])).
% 0.19/0.55  thf('8', plain,
% 0.19/0.55      (![X3 : $i, X5 : $i]:
% 0.19/0.55         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.55  thf('9', plain,
% 0.19/0.55      (![X3 : $i, X5 : $i]:
% 0.19/0.55         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.55  thf('10', plain,
% 0.19/0.55      (![X3 : $i, X5 : $i]:
% 0.19/0.55         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.55  thf('11', plain,
% 0.19/0.55      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.55  thf('12', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.19/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.55  thf(t28_xboole_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.55  thf('13', plain,
% 0.19/0.55      (![X17 : $i, X18 : $i]:
% 0.19/0.55         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.19/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.55  thf('14', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.55  thf('15', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.55  thf(t100_xboole_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.55  thf('16', plain,
% 0.19/0.55      (![X12 : $i, X13 : $i]:
% 0.19/0.55         ((k4_xboole_0 @ X12 @ X13)
% 0.19/0.55           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.55  thf('17', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((k4_xboole_0 @ X0 @ X1)
% 0.19/0.55           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.55      inference('sup+', [status(thm)], ['15', '16'])).
% 0.19/0.55  thf('18', plain,
% 0.19/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.19/0.55      inference('sup+', [status(thm)], ['14', '17'])).
% 0.19/0.55  thf(d5_xboole_0, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.19/0.55       ( ![D:$i]:
% 0.19/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.55           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.19/0.55  thf('19', plain,
% 0.19/0.55      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X10 @ X9)
% 0.19/0.55          | (r2_hidden @ X10 @ X7)
% 0.19/0.55          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.19/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.55  thf('20', plain,
% 0.19/0.55      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.19/0.55         ((r2_hidden @ X10 @ X7)
% 0.19/0.55          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.55  thf('21', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['18', '20'])).
% 0.19/0.55  thf('22', plain,
% 0.19/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.19/0.55      inference('sup+', [status(thm)], ['14', '17'])).
% 0.19/0.55  thf('23', plain,
% 0.19/0.55      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X10 @ X9)
% 0.19/0.55          | ~ (r2_hidden @ X10 @ X8)
% 0.19/0.55          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.19/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.55  thf('24', plain,
% 0.19/0.55      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X10 @ X8)
% 0.19/0.55          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['23'])).
% 0.19/0.55  thf('25', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.19/0.55          | ~ (r2_hidden @ X1 @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['22', '24'])).
% 0.19/0.55  thf('26', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.19/0.55      inference('clc', [status(thm)], ['21', '25'])).
% 0.19/0.55  thf('27', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 0.19/0.55      inference('sup-', [status(thm)], ['8', '26'])).
% 0.19/0.55  thf(t12_xboole_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.19/0.55  thf('28', plain,
% 0.19/0.55      (![X14 : $i, X15 : $i]:
% 0.19/0.55         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.19/0.55      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.19/0.55  thf('29', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.55  thf('30', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.19/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.19/0.55  thf('31', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.19/0.55      inference('sup+', [status(thm)], ['29', '30'])).
% 0.19/0.55  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.55  thf('32', plain, (![X27 : $i]: ((k1_subset_1 @ X27) = (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.19/0.55  thf('33', plain,
% 0.19/0.55      ((((sk_B) = (k1_subset_1 @ sk_A))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.55      inference('split', [status(esa)], ['2'])).
% 0.19/0.55  thf('34', plain,
% 0.19/0.55      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.55      inference('sup+', [status(thm)], ['32', '33'])).
% 0.19/0.55  thf('35', plain,
% 0.19/0.55      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.19/0.55         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.19/0.55      inference('split', [status(esa)], ['6'])).
% 0.19/0.55  thf('36', plain,
% 0.19/0.55      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.19/0.55         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.19/0.55             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.55  thf('37', plain,
% 0.19/0.55      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.55      inference('sup+', [status(thm)], ['32', '33'])).
% 0.19/0.55  thf('38', plain,
% 0.19/0.55      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.19/0.55         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.19/0.55             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.55      inference('demod', [status(thm)], ['36', '37'])).
% 0.19/0.55  thf('39', plain,
% 0.19/0.55      ((![X0 : $i]:
% 0.19/0.55          ~ (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ 
% 0.19/0.55             (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.19/0.55         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.19/0.55             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['31', '38'])).
% 0.19/0.55  thf('40', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 0.19/0.55      inference('sup-', [status(thm)], ['8', '26'])).
% 0.19/0.55  thf('41', plain,
% 0.19/0.55      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.19/0.55       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.19/0.55      inference('demod', [status(thm)], ['39', '40'])).
% 0.19/0.55  thf('42', plain,
% 0.19/0.55      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.19/0.55       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.19/0.55      inference('split', [status(esa)], ['2'])).
% 0.19/0.55  thf('43', plain, (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.19/0.55      inference('sat_resolution*', [status(thm)], ['7', '41', '42'])).
% 0.19/0.55  thf('44', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.19/0.55          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.19/0.55      inference('simpl_trail', [status(thm)], ['5', '43'])).
% 0.19/0.55  thf('45', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(d2_subset_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( ( v1_xboole_0 @ A ) =>
% 0.19/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.19/0.55       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.55  thf('46', plain,
% 0.19/0.55      (![X24 : $i, X25 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X24 @ X25)
% 0.19/0.55          | (r2_hidden @ X24 @ X25)
% 0.19/0.55          | (v1_xboole_0 @ X25))),
% 0.19/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.19/0.55  thf('47', plain,
% 0.19/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.19/0.55        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.55  thf(fc1_subset_1, axiom,
% 0.19/0.55    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.55  thf('48', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 0.19/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.19/0.55  thf('49', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.55      inference('clc', [status(thm)], ['47', '48'])).
% 0.19/0.55  thf(d1_zfmisc_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.19/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.19/0.55  thf('50', plain,
% 0.19/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X22 @ X21)
% 0.19/0.55          | (r1_tarski @ X22 @ X20)
% 0.19/0.55          | ((X21) != (k1_zfmisc_1 @ X20)))),
% 0.19/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.55  thf('51', plain,
% 0.19/0.55      (![X20 : $i, X22 : $i]:
% 0.19/0.55         ((r1_tarski @ X22 @ X20) | ~ (r2_hidden @ X22 @ (k1_zfmisc_1 @ X20)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['50'])).
% 0.19/0.55  thf('52', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.19/0.55      inference('sup-', [status(thm)], ['49', '51'])).
% 0.19/0.55  thf('53', plain,
% 0.19/0.55      (![X17 : $i, X18 : $i]:
% 0.19/0.55         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.19/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.55  thf('54', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.19/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.19/0.55  thf('55', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.55  thf('56', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.19/0.55      inference('demod', [status(thm)], ['54', '55'])).
% 0.19/0.55  thf('57', plain,
% 0.19/0.55      (![X12 : $i, X13 : $i]:
% 0.19/0.55         ((k4_xboole_0 @ X12 @ X13)
% 0.19/0.55           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.55  thf('58', plain,
% 0.19/0.55      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.55      inference('sup+', [status(thm)], ['56', '57'])).
% 0.19/0.55  thf('59', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(d5_subset_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.19/0.55  thf('60', plain,
% 0.19/0.55      (![X28 : $i, X29 : $i]:
% 0.19/0.55         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 0.19/0.55          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.19/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.55  thf('61', plain,
% 0.19/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.55      inference('sup-', [status(thm)], ['59', '60'])).
% 0.19/0.55  thf('62', plain,
% 0.19/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.55      inference('sup+', [status(thm)], ['58', '61'])).
% 0.19/0.55  thf('63', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((r2_hidden @ X0 @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.19/0.55          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.19/0.55      inference('demod', [status(thm)], ['44', '62'])).
% 0.19/0.55  thf('64', plain,
% 0.19/0.55      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.55      inference('sup+', [status(thm)], ['56', '57'])).
% 0.19/0.55  thf('65', plain,
% 0.19/0.55      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X10 @ X8)
% 0.19/0.55          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['23'])).
% 0.19/0.55  thf('66', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.19/0.55          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.19/0.55      inference('sup-', [status(thm)], ['64', '65'])).
% 0.19/0.55  thf('67', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.19/0.55      inference('clc', [status(thm)], ['63', '66'])).
% 0.19/0.55  thf('68', plain, (![X0 : $i]: (r1_tarski @ sk_B @ X0)),
% 0.19/0.55      inference('sup-', [status(thm)], ['1', '67'])).
% 0.19/0.55  thf('69', plain,
% 0.19/0.55      (![X14 : $i, X15 : $i]:
% 0.19/0.55         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.19/0.55      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.19/0.55  thf('70', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['68', '69'])).
% 0.19/0.55  thf('71', plain, (((sk_B) = (k1_xboole_0))),
% 0.19/0.55      inference('sup+', [status(thm)], ['0', '70'])).
% 0.19/0.55  thf('72', plain,
% 0.19/0.55      ((((sk_B) != (k1_subset_1 @ sk_A)))
% 0.19/0.55         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.55      inference('split', [status(esa)], ['6'])).
% 0.19/0.55  thf('73', plain, (![X27 : $i]: ((k1_subset_1 @ X27) = (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.19/0.55  thf('74', plain,
% 0.19/0.55      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.19/0.55      inference('demod', [status(thm)], ['72', '73'])).
% 0.19/0.55  thf('75', plain, (~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.19/0.55      inference('sat_resolution*', [status(thm)], ['7', '41'])).
% 0.19/0.55  thf('76', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.55      inference('simpl_trail', [status(thm)], ['74', '75'])).
% 0.19/0.55  thf('77', plain, ($false),
% 0.19/0.55      inference('simplify_reflect-', [status(thm)], ['71', '76'])).
% 0.19/0.55  
% 0.19/0.55  % SZS output end Refutation
% 0.19/0.55  
% 0.19/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
