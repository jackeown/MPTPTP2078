%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2I3RyvZ8Jl

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:33 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 330 expanded)
%              Number of leaves         :   24 ( 103 expanded)
%              Depth                    :   19
%              Number of atoms          :  784 (2671 expanded)
%              Number of equality atoms :   66 ( 229 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t39_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
        <=> ( B
            = ( k2_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_subset_1])).

thf('0',plain,(
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

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X29: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( r1_tarski @ X21 @ X19 )
      | ( X20
       != ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_tarski @ X21 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ X8 @ X11 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','18'])).

thf('20',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ X12 @ X9 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('38',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('41',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('42',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['39','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['26','44'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('46',plain,(
    ! [X26: $i] :
      ( ( k2_subset_1 @ X26 )
      = X26 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('47',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('48',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('52',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('54',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k5_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('56',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf('57',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('59',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','60'])).

thf('62',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('63',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['25','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['23','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('67',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['64','69'])).

thf('71',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('72',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('73',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['19','74'])).

thf('76',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('77',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('80',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    sk_B = sk_A ),
    inference('sup+',[status(thm)],['11','80'])).

thf('82',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['24'])).

thf('83',plain,(
    ! [X26: $i] :
      ( ( k2_subset_1 @ X26 )
      = X26 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('84',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['25','61'])).

thf('86',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['84','85'])).

thf('87',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['81','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2I3RyvZ8Jl
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:45:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.97  % Solved by: fo/fo7.sh
% 0.75/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.97  % done 1140 iterations in 0.537s
% 0.75/0.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.97  % SZS output start Refutation
% 0.75/0.97  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.75/0.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.97  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.75/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.97  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.75/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.97  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.97  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.75/0.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.97  thf(t39_subset_1, conjecture,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.97       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.75/0.97         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.75/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.97    (~( ![A:$i,B:$i]:
% 0.75/0.97        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.97          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.75/0.97            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.75/0.97    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.75/0.97  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf(d2_subset_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( ( v1_xboole_0 @ A ) =>
% 0.75/0.97         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.75/0.97       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.75/0.97         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.75/0.97  thf('1', plain,
% 0.75/0.97      (![X23 : $i, X24 : $i]:
% 0.75/0.97         (~ (m1_subset_1 @ X23 @ X24)
% 0.75/0.97          | (r2_hidden @ X23 @ X24)
% 0.75/0.97          | (v1_xboole_0 @ X24))),
% 0.75/0.97      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.75/0.97  thf('2', plain,
% 0.75/0.97      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.75/0.97        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.97  thf(fc1_subset_1, axiom,
% 0.75/0.97    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.75/0.97  thf('3', plain, (![X29 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 0.75/0.97      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.75/0.97  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.97      inference('clc', [status(thm)], ['2', '3'])).
% 0.75/0.97  thf(d1_zfmisc_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.75/0.97       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.75/0.97  thf('5', plain,
% 0.75/0.97      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X21 @ X20)
% 0.75/0.97          | (r1_tarski @ X21 @ X19)
% 0.75/0.97          | ((X20) != (k1_zfmisc_1 @ X19)))),
% 0.75/0.97      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.75/0.97  thf('6', plain,
% 0.75/0.97      (![X19 : $i, X21 : $i]:
% 0.75/0.97         ((r1_tarski @ X21 @ X19) | ~ (r2_hidden @ X21 @ (k1_zfmisc_1 @ X19)))),
% 0.75/0.97      inference('simplify', [status(thm)], ['5'])).
% 0.75/0.97  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.75/0.97      inference('sup-', [status(thm)], ['4', '6'])).
% 0.75/0.97  thf(t28_xboole_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.75/0.97  thf('8', plain,
% 0.75/0.97      (![X16 : $i, X17 : $i]:
% 0.75/0.97         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.75/0.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.75/0.97  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.75/0.97      inference('sup-', [status(thm)], ['7', '8'])).
% 0.75/0.97  thf(commutativity_k3_xboole_0, axiom,
% 0.75/0.97    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.75/0.97  thf('10', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.97  thf('11', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.75/0.97      inference('demod', [status(thm)], ['9', '10'])).
% 0.75/0.97  thf('12', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.75/0.97      inference('demod', [status(thm)], ['9', '10'])).
% 0.75/0.97  thf(t100_xboole_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/0.97  thf('13', plain,
% 0.75/0.97      (![X14 : $i, X15 : $i]:
% 0.75/0.97         ((k4_xboole_0 @ X14 @ X15)
% 0.75/0.97           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.97  thf('14', plain,
% 0.75/0.97      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.75/0.97      inference('sup+', [status(thm)], ['12', '13'])).
% 0.75/0.97  thf(d3_tarski, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( r1_tarski @ A @ B ) <=>
% 0.75/0.97       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.75/0.97  thf('15', plain,
% 0.75/0.97      (![X5 : $i, X7 : $i]:
% 0.75/0.97         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.75/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.97  thf(d5_xboole_0, axiom,
% 0.75/0.97    (![A:$i,B:$i,C:$i]:
% 0.75/0.97     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.75/0.97       ( ![D:$i]:
% 0.75/0.97         ( ( r2_hidden @ D @ C ) <=>
% 0.75/0.97           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.75/0.97  thf('16', plain,
% 0.75/0.97      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X8 @ X9)
% 0.75/0.97          | (r2_hidden @ X8 @ X10)
% 0.75/0.97          | (r2_hidden @ X8 @ X11)
% 0.75/0.97          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.75/0.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.97  thf('17', plain,
% 0.75/0.97      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.75/0.97         ((r2_hidden @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 0.75/0.97          | (r2_hidden @ X8 @ X10)
% 0.75/0.97          | ~ (r2_hidden @ X8 @ X9))),
% 0.75/0.97      inference('simplify', [status(thm)], ['16'])).
% 0.75/0.97  thf('18', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.97         ((r1_tarski @ X0 @ X1)
% 0.75/0.97          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.75/0.97          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['15', '17'])).
% 0.75/0.97  thf('19', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.75/0.97          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B)
% 0.75/0.97          | (r1_tarski @ sk_A @ X0))),
% 0.75/0.97      inference('sup+', [status(thm)], ['14', '18'])).
% 0.75/0.97  thf('20', plain,
% 0.75/0.97      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.75/0.97        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('21', plain,
% 0.75/0.97      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.75/0.97         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.75/0.97      inference('split', [status(esa)], ['20'])).
% 0.75/0.97  thf('22', plain,
% 0.75/0.97      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X4 @ X5)
% 0.75/0.97          | (r2_hidden @ X4 @ X6)
% 0.75/0.97          | ~ (r1_tarski @ X5 @ X6))),
% 0.75/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.97  thf('23', plain,
% 0.75/0.97      ((![X0 : $i]:
% 0.75/0.97          ((r2_hidden @ X0 @ sk_B)
% 0.75/0.97           | ~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.75/0.97         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['21', '22'])).
% 0.75/0.97  thf('24', plain,
% 0.75/0.97      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.75/0.97        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('25', plain,
% 0.75/0.97      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.75/0.97       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.75/0.97      inference('split', [status(esa)], ['24'])).
% 0.75/0.97  thf('26', plain,
% 0.75/0.97      (![X5 : $i, X7 : $i]:
% 0.75/0.97         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.75/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.97  thf('27', plain,
% 0.75/0.97      (![X5 : $i, X7 : $i]:
% 0.75/0.97         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.75/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.97  thf('28', plain,
% 0.75/0.97      (![X5 : $i, X7 : $i]:
% 0.75/0.97         ((r1_tarski @ X5 @ X7) | ~ (r2_hidden @ (sk_C @ X7 @ X5) @ X7))),
% 0.75/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.97  thf('29', plain,
% 0.75/0.97      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['27', '28'])).
% 0.75/0.97  thf('30', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.75/0.97      inference('simplify', [status(thm)], ['29'])).
% 0.75/0.97  thf('31', plain,
% 0.75/0.97      (![X16 : $i, X17 : $i]:
% 0.75/0.97         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.75/0.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.75/0.97  thf('32', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['30', '31'])).
% 0.75/0.97  thf('33', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.97  thf('34', plain,
% 0.75/0.97      (![X14 : $i, X15 : $i]:
% 0.75/0.97         ((k4_xboole_0 @ X14 @ X15)
% 0.75/0.97           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.97  thf('35', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k4_xboole_0 @ X0 @ X1)
% 0.75/0.97           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.75/0.97      inference('sup+', [status(thm)], ['33', '34'])).
% 0.75/0.97  thf('36', plain,
% 0.75/0.97      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.97      inference('sup+', [status(thm)], ['32', '35'])).
% 0.75/0.97  thf('37', plain,
% 0.75/0.97      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X12 @ X11)
% 0.75/0.97          | (r2_hidden @ X12 @ X9)
% 0.75/0.97          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.75/0.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.97  thf('38', plain,
% 0.75/0.97      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.75/0.97         ((r2_hidden @ X12 @ X9)
% 0.75/0.97          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.75/0.97      inference('simplify', [status(thm)], ['37'])).
% 0.75/0.97  thf('39', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['36', '38'])).
% 0.75/0.97  thf('40', plain,
% 0.75/0.97      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.97      inference('sup+', [status(thm)], ['32', '35'])).
% 0.75/0.97  thf('41', plain,
% 0.75/0.97      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X12 @ X11)
% 0.75/0.97          | ~ (r2_hidden @ X12 @ X10)
% 0.75/0.97          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.75/0.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.97  thf('42', plain,
% 0.75/0.97      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X12 @ X10)
% 0.75/0.97          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.75/0.97      inference('simplify', [status(thm)], ['41'])).
% 0.75/0.97  thf('43', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.75/0.97          | ~ (r2_hidden @ X1 @ X0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['40', '42'])).
% 0.75/0.97  thf('44', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.97      inference('clc', [status(thm)], ['39', '43'])).
% 0.75/0.97  thf('45', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 0.75/0.97      inference('sup-', [status(thm)], ['26', '44'])).
% 0.75/0.97  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.75/0.97  thf('46', plain, (![X26 : $i]: ((k2_subset_1 @ X26) = (X26))),
% 0.75/0.97      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.75/0.97  thf('47', plain,
% 0.75/0.97      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.75/0.97      inference('split', [status(esa)], ['20'])).
% 0.75/0.97  thf('48', plain,
% 0.75/0.97      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.75/0.97      inference('sup+', [status(thm)], ['46', '47'])).
% 0.75/0.97  thf('49', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('50', plain,
% 0.75/0.97      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.75/0.97         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.75/0.97      inference('sup+', [status(thm)], ['48', '49'])).
% 0.75/0.97  thf(d5_subset_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.97       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.75/0.97  thf('51', plain,
% 0.75/0.97      (![X27 : $i, X28 : $i]:
% 0.75/0.97         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 0.75/0.97          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.75/0.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.75/0.97  thf('52', plain,
% 0.75/0.97      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.75/0.97         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.75/0.97      inference('sup-', [status(thm)], ['50', '51'])).
% 0.75/0.97  thf('53', plain,
% 0.75/0.97      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.97      inference('sup+', [status(thm)], ['32', '35'])).
% 0.75/0.97  thf('54', plain,
% 0.75/0.97      ((((k3_subset_1 @ sk_A @ sk_A) = (k5_xboole_0 @ sk_A @ sk_A)))
% 0.75/0.97         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.75/0.97      inference('demod', [status(thm)], ['52', '53'])).
% 0.75/0.97  thf('55', plain,
% 0.75/0.97      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.75/0.97      inference('sup+', [status(thm)], ['46', '47'])).
% 0.75/0.97  thf('56', plain,
% 0.75/0.97      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.75/0.97         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.75/0.97      inference('split', [status(esa)], ['24'])).
% 0.75/0.97  thf('57', plain,
% 0.75/0.97      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.75/0.97         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.75/0.97             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.75/0.97      inference('sup-', [status(thm)], ['55', '56'])).
% 0.75/0.97  thf('58', plain,
% 0.75/0.97      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.75/0.97      inference('sup+', [status(thm)], ['46', '47'])).
% 0.75/0.97  thf('59', plain,
% 0.75/0.97      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.75/0.97         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.75/0.97             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.75/0.97      inference('demod', [status(thm)], ['57', '58'])).
% 0.75/0.97  thf('60', plain,
% 0.75/0.97      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_A) @ sk_A))
% 0.75/0.97         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.75/0.97             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.75/0.97      inference('sup-', [status(thm)], ['54', '59'])).
% 0.75/0.97  thf('61', plain,
% 0.75/0.97      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.75/0.97       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['45', '60'])).
% 0.75/0.97  thf('62', plain,
% 0.75/0.97      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.75/0.97       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.75/0.97      inference('split', [status(esa)], ['20'])).
% 0.75/0.97  thf('63', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.75/0.97      inference('sat_resolution*', [status(thm)], ['25', '61', '62'])).
% 0.75/0.97  thf('64', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         ((r2_hidden @ X0 @ sk_B)
% 0.75/0.97          | ~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.75/0.97      inference('simpl_trail', [status(thm)], ['23', '63'])).
% 0.75/0.97  thf('65', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('66', plain,
% 0.75/0.97      (![X27 : $i, X28 : $i]:
% 0.75/0.97         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 0.75/0.97          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.75/0.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.75/0.97  thf('67', plain,
% 0.75/0.97      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.75/0.97      inference('sup-', [status(thm)], ['65', '66'])).
% 0.75/0.97  thf('68', plain,
% 0.75/0.97      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X12 @ X10)
% 0.75/0.97          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.75/0.97      inference('simplify', [status(thm)], ['41'])).
% 0.75/0.97  thf('69', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.75/0.97          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.75/0.97      inference('sup-', [status(thm)], ['67', '68'])).
% 0.75/0.97  thf('70', plain,
% 0.75/0.97      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.75/0.97      inference('clc', [status(thm)], ['64', '69'])).
% 0.75/0.97  thf('71', plain,
% 0.75/0.97      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.75/0.97      inference('sup+', [status(thm)], ['12', '13'])).
% 0.75/0.97  thf('72', plain,
% 0.75/0.97      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.75/0.97      inference('sup-', [status(thm)], ['65', '66'])).
% 0.75/0.97  thf('73', plain,
% 0.75/0.97      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.75/0.97      inference('sup+', [status(thm)], ['71', '72'])).
% 0.75/0.97  thf('74', plain,
% 0.75/0.97      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_A @ sk_B))),
% 0.75/0.97      inference('demod', [status(thm)], ['70', '73'])).
% 0.75/0.97  thf('75', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.75/0.97      inference('clc', [status(thm)], ['19', '74'])).
% 0.75/0.97  thf('76', plain,
% 0.75/0.97      (![X5 : $i, X7 : $i]:
% 0.75/0.97         ((r1_tarski @ X5 @ X7) | ~ (r2_hidden @ (sk_C @ X7 @ X5) @ X7))),
% 0.75/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.97  thf('77', plain, (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 0.75/0.97      inference('sup-', [status(thm)], ['75', '76'])).
% 0.75/0.97  thf('78', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.75/0.97      inference('simplify', [status(thm)], ['77'])).
% 0.75/0.97  thf('79', plain,
% 0.75/0.97      (![X16 : $i, X17 : $i]:
% 0.75/0.97         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.75/0.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.75/0.97  thf('80', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.75/0.97      inference('sup-', [status(thm)], ['78', '79'])).
% 0.75/0.97  thf('81', plain, (((sk_B) = (sk_A))),
% 0.75/0.97      inference('sup+', [status(thm)], ['11', '80'])).
% 0.75/0.97  thf('82', plain,
% 0.75/0.97      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.75/0.97         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.75/0.97      inference('split', [status(esa)], ['24'])).
% 0.75/0.97  thf('83', plain, (![X26 : $i]: ((k2_subset_1 @ X26) = (X26))),
% 0.75/0.97      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.75/0.97  thf('84', plain,
% 0.75/0.97      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.75/0.97      inference('demod', [status(thm)], ['82', '83'])).
% 0.75/0.97  thf('85', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.75/0.97      inference('sat_resolution*', [status(thm)], ['25', '61'])).
% 0.75/0.97  thf('86', plain, (((sk_B) != (sk_A))),
% 0.75/0.97      inference('simpl_trail', [status(thm)], ['84', '85'])).
% 0.75/0.97  thf('87', plain, ($false),
% 0.75/0.97      inference('simplify_reflect-', [status(thm)], ['81', '86'])).
% 0.75/0.97  
% 0.75/0.97  % SZS output end Refutation
% 0.75/0.97  
% 0.75/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
