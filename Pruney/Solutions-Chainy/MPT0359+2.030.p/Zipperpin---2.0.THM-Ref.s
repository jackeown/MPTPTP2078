%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tRDycu42Qx

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 284 expanded)
%              Number of leaves         :   34 (  92 expanded)
%              Depth                    :   15
%              Number of atoms          :  691 (2234 expanded)
%              Number of equality atoms :   76 ( 220 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( r1_tarski @ X19 @ X17 )
      | ( X18
       != ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_tarski @ X19 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
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

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('18',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('21',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X32 @ ( k3_subset_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('22',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('25',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('27',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k3_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['22','27'])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ X34 @ ( k3_subset_1 @ X33 @ X34 ) )
      | ( X34
        = ( k1_subset_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( ( k5_xboole_0 @ sk_A @ sk_B )
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['33'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('35',plain,(
    ! [X25: $i] :
      ( ( k2_subset_1 @ X25 )
      = X25 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('36',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['31'])).

thf('37',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('41',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('42',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('47',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['33'])).

thf('48',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('50',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('52',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['31'])).

thf('55',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['34','53','54'])).

thf('56',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['32','55'])).

thf('57',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('58',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('60',plain,(
    ! [X28: $i,X29: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('61',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('63',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('64',plain,(
    ! [X24: $i] :
      ( ( k1_subset_1 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('65',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['30','58','63','64'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('66',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('67',plain,(
    sk_A = sk_B ),
    inference(demod,[status(thm)],['19','65','66'])).

thf('68',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['33'])).

thf('69',plain,(
    ! [X25: $i] :
      ( ( k2_subset_1 @ X25 )
      = X25 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('70',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['34','53'])).

thf('72',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['67','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tRDycu42Qx
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:39:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 285 iterations in 0.081s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.57  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.57  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.57  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.22/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.57  thf(t39_subset_1, conjecture,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.22/0.57         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i,B:$i]:
% 0.22/0.57        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.22/0.57            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.22/0.57  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(d2_subset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ( v1_xboole_0 @ A ) =>
% 0.22/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.22/0.57       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.57  thf('1', plain,
% 0.22/0.57      (![X21 : $i, X22 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X21 @ X22)
% 0.22/0.57          | (r2_hidden @ X21 @ X22)
% 0.22/0.57          | (v1_xboole_0 @ X22))),
% 0.22/0.57      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.57  thf('2', plain,
% 0.22/0.57      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.57        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.57  thf(fc1_subset_1, axiom,
% 0.22/0.57    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.57  thf('3', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 0.22/0.57      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.57  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('clc', [status(thm)], ['2', '3'])).
% 0.22/0.57  thf(d1_zfmisc_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.57  thf('5', plain,
% 0.22/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X19 @ X18)
% 0.22/0.57          | (r1_tarski @ X19 @ X17)
% 0.22/0.57          | ((X18) != (k1_zfmisc_1 @ X17)))),
% 0.22/0.57      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.57  thf('6', plain,
% 0.22/0.57      (![X17 : $i, X19 : $i]:
% 0.22/0.57         ((r1_tarski @ X19 @ X17) | ~ (r2_hidden @ X19 @ (k1_zfmisc_1 @ X17)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.57  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.22/0.57      inference('sup-', [status(thm)], ['4', '6'])).
% 0.22/0.57  thf(t28_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.57  thf('8', plain,
% 0.22/0.57      (![X8 : $i, X9 : $i]:
% 0.22/0.57         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.22/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.57  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.57  thf('10', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.57  thf('11', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.22/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.57  thf(t100_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      (![X4 : $i, X5 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X4 @ X5)
% 0.22/0.57           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.57  thf('13', plain,
% 0.22/0.57      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.57      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.57  thf(t98_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.22/0.57  thf('14', plain,
% 0.22/0.57      (![X14 : $i, X15 : $i]:
% 0.22/0.57         ((k2_xboole_0 @ X14 @ X15)
% 0.22/0.57           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.22/0.57  thf('15', plain,
% 0.22/0.57      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.22/0.57         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['13', '14'])).
% 0.22/0.57  thf('16', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.22/0.57      inference('sup-', [status(thm)], ['4', '6'])).
% 0.22/0.57  thf(t12_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.57  thf('17', plain,
% 0.22/0.57      (![X6 : $i, X7 : $i]:
% 0.22/0.57         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.22/0.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.57  thf('18', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.57  thf('19', plain,
% 0.22/0.57      (((sk_A) = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.57      inference('demod', [status(thm)], ['15', '18'])).
% 0.22/0.57  thf('20', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(involutiveness_k3_subset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      (![X31 : $i, X32 : $i]:
% 0.22/0.57         (((k3_subset_1 @ X32 @ (k3_subset_1 @ X32 @ X31)) = (X31))
% 0.22/0.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 0.22/0.57      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.57  thf('22', plain,
% 0.22/0.57      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.57  thf('23', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(d5_subset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.57  thf('24', plain,
% 0.22/0.57      (![X26 : $i, X27 : $i]:
% 0.22/0.57         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 0.22/0.57          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.22/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.57  thf('25', plain,
% 0.22/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.57  thf('26', plain,
% 0.22/0.57      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.57      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.57  thf('27', plain,
% 0.22/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.57  thf('28', plain,
% 0.22/0.57      (((k3_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.22/0.57      inference('demod', [status(thm)], ['22', '27'])).
% 0.22/0.57  thf(t38_subset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.22/0.57         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.22/0.57  thf('29', plain,
% 0.22/0.57      (![X33 : $i, X34 : $i]:
% 0.22/0.57         (~ (r1_tarski @ X34 @ (k3_subset_1 @ X33 @ X34))
% 0.22/0.57          | ((X34) = (k1_subset_1 @ X33))
% 0.22/0.57          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t38_subset_1])).
% 0.22/0.57  thf('30', plain,
% 0.22/0.57      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 0.22/0.57        | ~ (m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.57        | ((k5_xboole_0 @ sk_A @ sk_B) = (k1_subset_1 @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.57  thf('31', plain,
% 0.22/0.57      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.22/0.57        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('32', plain,
% 0.22/0.57      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.22/0.57         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.22/0.57      inference('split', [status(esa)], ['31'])).
% 0.22/0.57  thf('33', plain,
% 0.22/0.57      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.22/0.57        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('34', plain,
% 0.22/0.57      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.22/0.57       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.22/0.57      inference('split', [status(esa)], ['33'])).
% 0.22/0.57  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.57  thf('35', plain, (![X25 : $i]: ((k2_subset_1 @ X25) = (X25))),
% 0.22/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.57  thf('36', plain,
% 0.22/0.57      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.57      inference('split', [status(esa)], ['31'])).
% 0.22/0.57  thf('37', plain,
% 0.22/0.57      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.57      inference('sup+', [status(thm)], ['35', '36'])).
% 0.22/0.57  thf('38', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('39', plain,
% 0.22/0.57      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.22/0.57         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.57      inference('sup+', [status(thm)], ['37', '38'])).
% 0.22/0.57  thf('40', plain,
% 0.22/0.57      (![X26 : $i, X27 : $i]:
% 0.22/0.57         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 0.22/0.57          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.22/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.57  thf('41', plain,
% 0.22/0.57      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.22/0.57         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.57  thf(idempotence_k2_xboole_0, axiom,
% 0.22/0.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.57  thf('42', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.22/0.57      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.22/0.57  thf(t46_xboole_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.22/0.57  thf('43', plain,
% 0.22/0.57      (![X11 : $i, X12 : $i]:
% 0.22/0.57         ((k4_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.22/0.57  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.57      inference('sup+', [status(thm)], ['42', '43'])).
% 0.22/0.57  thf('45', plain,
% 0.22/0.57      ((((k3_subset_1 @ sk_A @ sk_A) = (k1_xboole_0)))
% 0.22/0.57         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.57      inference('demod', [status(thm)], ['41', '44'])).
% 0.22/0.57  thf('46', plain,
% 0.22/0.57      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.57      inference('sup+', [status(thm)], ['35', '36'])).
% 0.22/0.57  thf('47', plain,
% 0.22/0.57      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.22/0.57         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.22/0.57      inference('split', [status(esa)], ['33'])).
% 0.22/0.57  thf('48', plain,
% 0.22/0.57      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.22/0.57         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.22/0.57             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.57  thf('49', plain,
% 0.22/0.57      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.57      inference('sup+', [status(thm)], ['35', '36'])).
% 0.22/0.57  thf('50', plain,
% 0.22/0.57      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.22/0.57         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.22/0.57             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.57      inference('demod', [status(thm)], ['48', '49'])).
% 0.22/0.57  thf('51', plain,
% 0.22/0.57      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.22/0.57         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.22/0.57             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['45', '50'])).
% 0.22/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.57  thf('52', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.22/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.57  thf('53', plain,
% 0.22/0.57      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.22/0.57       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.22/0.57      inference('demod', [status(thm)], ['51', '52'])).
% 0.22/0.57  thf('54', plain,
% 0.22/0.57      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.22/0.57       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.22/0.57      inference('split', [status(esa)], ['31'])).
% 0.22/0.57  thf('55', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.22/0.57      inference('sat_resolution*', [status(thm)], ['34', '53', '54'])).
% 0.22/0.57  thf('56', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)),
% 0.22/0.57      inference('simpl_trail', [status(thm)], ['32', '55'])).
% 0.22/0.57  thf('57', plain,
% 0.22/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.57  thf('58', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.22/0.57      inference('demod', [status(thm)], ['56', '57'])).
% 0.22/0.57  thf('59', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(dt_k3_subset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.57  thf('60', plain,
% 0.22/0.57      (![X28 : $i, X29 : $i]:
% 0.22/0.57         ((m1_subset_1 @ (k3_subset_1 @ X28 @ X29) @ (k1_zfmisc_1 @ X28))
% 0.22/0.57          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.22/0.57      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.57  thf('61', plain,
% 0.22/0.57      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.57  thf('62', plain,
% 0.22/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.57  thf('63', plain,
% 0.22/0.57      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.57      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.57  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.57  thf('64', plain, (![X24 : $i]: ((k1_subset_1 @ X24) = (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.57  thf('65', plain, (((k5_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.57      inference('demod', [status(thm)], ['30', '58', '63', '64'])).
% 0.22/0.57  thf(t5_boole, axiom,
% 0.22/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.57  thf('66', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.22/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.57  thf('67', plain, (((sk_A) = (sk_B))),
% 0.22/0.57      inference('demod', [status(thm)], ['19', '65', '66'])).
% 0.22/0.57  thf('68', plain,
% 0.22/0.57      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.22/0.57         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.57      inference('split', [status(esa)], ['33'])).
% 0.22/0.57  thf('69', plain, (![X25 : $i]: ((k2_subset_1 @ X25) = (X25))),
% 0.22/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.57  thf('70', plain,
% 0.22/0.57      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.22/0.57      inference('demod', [status(thm)], ['68', '69'])).
% 0.22/0.57  thf('71', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.22/0.57      inference('sat_resolution*', [status(thm)], ['34', '53'])).
% 0.22/0.57  thf('72', plain, (((sk_B) != (sk_A))),
% 0.22/0.57      inference('simpl_trail', [status(thm)], ['70', '71'])).
% 0.22/0.57  thf('73', plain, ($false),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['67', '72'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.22/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
