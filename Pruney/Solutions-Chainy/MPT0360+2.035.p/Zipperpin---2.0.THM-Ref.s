%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4KaISRoMJi

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:45 EST 2020

% Result     : Theorem 6.12s
% Output     : Refutation 6.12s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 262 expanded)
%              Number of leaves         :   35 (  92 expanded)
%              Depth                    :   21
%              Number of atoms          :  578 (1873 expanded)
%              Number of equality atoms :   37 ( 143 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ sk_A ) ),
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
    ! [X80: $i,X81: $i] :
      ( ~ ( m1_subset_1 @ X80 @ X81 )
      | ( r2_hidden @ X80 @ X81 )
      | ( v1_xboole_0 @ X81 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_3 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( r1_tarski @ X54 @ X55 )
      | ( r2_hidden @ X54 @ X56 )
      | ( X56
       != ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('8',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r2_hidden @ X54 @ ( k1_zfmisc_1 @ X55 ) )
      | ~ ( r1_tarski @ X54 @ X55 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X17: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['16','19'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X23: $i] :
      ( ( k4_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','22'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('25',plain,(
    ! [X73: $i,X74: $i,X75: $i] :
      ( ( X73 != X75 )
      | ~ ( r2_hidden @ X73 @ ( k4_xboole_0 @ X74 @ ( k1_tarski @ X75 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('26',plain,(
    ! [X74: $i,X75: $i] :
      ~ ( r2_hidden @ X75 @ ( k4_xboole_0 @ X74 @ ( k1_tarski @ X75 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','29'])).

thf('31',plain,(
    r2_hidden @ sk_C_3 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','30'])).

thf('32',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( r2_hidden @ X57 @ X56 )
      | ( r1_tarski @ X57 @ X55 )
      | ( X56
       != ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('33',plain,(
    ! [X55: $i,X57: $i] :
      ( ( r1_tarski @ X57 @ X55 )
      | ~ ( r2_hidden @ X57 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    r1_tarski @ sk_C_3 @ sk_A ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    r1_tarski @ sk_B_2 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ~ ( r1_tarski @ sk_C_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r2_hidden @ X54 @ ( k1_zfmisc_1 @ X55 ) )
      | ~ ( r1_tarski @ X54 @ X55 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('40',plain,(
    r2_hidden @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X80: $i,X81: $i] :
      ( ~ ( r2_hidden @ X80 @ X81 )
      | ( m1_subset_1 @ X80 @ X81 )
      | ( v1_xboole_0 @ X81 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','29'])).

thf('44',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('46',plain,(
    ! [X88: $i,X89: $i,X90: $i] :
      ( ~ ( m1_subset_1 @ X88 @ ( k1_zfmisc_1 @ X89 ) )
      | ~ ( r1_tarski @ X90 @ X88 )
      | ( r1_tarski @ ( k3_subset_1 @ X89 @ X88 ) @ ( k3_subset_1 @ X89 @ X90 ) )
      | ~ ( m1_subset_1 @ X90 @ ( k1_zfmisc_1 @ X89 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_3 ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r1_tarski @ sk_B_2 @ sk_C_3 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_3 ) @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    r1_tarski @ sk_B_2 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_3 ) @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('55',plain,(
    ! [X91: $i,X92: $i] :
      ( ~ ( r1_tarski @ X92 @ ( k3_subset_1 @ X91 @ X92 ) )
      | ( X92
        = ( k1_subset_1 @ X91 ) )
      | ~ ( m1_subset_1 @ X92 @ ( k1_zfmisc_1 @ X91 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf('56',plain,
    ( ~ ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B_2
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['42','43'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('58',plain,(
    ! [X83: $i] :
      ( ( k1_subset_1 @ X83 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('59',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4KaISRoMJi
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.12/6.36  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.12/6.36  % Solved by: fo/fo7.sh
% 6.12/6.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.12/6.36  % done 13091 iterations in 5.892s
% 6.12/6.36  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.12/6.36  % SZS output start Refutation
% 6.12/6.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.12/6.36  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.12/6.36  thf(sk_A_type, type, sk_A: $i).
% 6.12/6.36  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.12/6.36  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.12/6.36  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 6.12/6.36  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.12/6.36  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.12/6.36  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.12/6.36  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.12/6.36  thf(sk_C_3_type, type, sk_C_3: $i).
% 6.12/6.36  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.12/6.36  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.12/6.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.12/6.36  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.12/6.36  thf(sk_B_2_type, type, sk_B_2: $i).
% 6.12/6.36  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 6.12/6.36  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 6.12/6.36  thf(t40_subset_1, conjecture,
% 6.12/6.36    (![A:$i,B:$i,C:$i]:
% 6.12/6.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.12/6.36       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 6.12/6.36         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.12/6.36  thf(zf_stmt_0, negated_conjecture,
% 6.12/6.36    (~( ![A:$i,B:$i,C:$i]:
% 6.12/6.36        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.12/6.36          ( ( ( r1_tarski @ B @ C ) & 
% 6.12/6.36              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 6.12/6.36            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 6.12/6.36    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 6.12/6.36  thf('0', plain, ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ sk_A))),
% 6.12/6.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.36  thf(d2_subset_1, axiom,
% 6.12/6.36    (![A:$i,B:$i]:
% 6.12/6.36     ( ( ( v1_xboole_0 @ A ) =>
% 6.12/6.36         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 6.12/6.36       ( ( ~( v1_xboole_0 @ A ) ) =>
% 6.12/6.36         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 6.12/6.36  thf('1', plain,
% 6.12/6.36      (![X80 : $i, X81 : $i]:
% 6.12/6.36         (~ (m1_subset_1 @ X80 @ X81)
% 6.12/6.36          | (r2_hidden @ X80 @ X81)
% 6.12/6.36          | (v1_xboole_0 @ X81))),
% 6.12/6.36      inference('cnf', [status(esa)], [d2_subset_1])).
% 6.12/6.36  thf('2', plain,
% 6.12/6.36      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 6.12/6.36        | (r2_hidden @ sk_C_3 @ (k1_zfmisc_1 @ sk_A)))),
% 6.12/6.36      inference('sup-', [status(thm)], ['0', '1'])).
% 6.12/6.36  thf(d3_tarski, axiom,
% 6.12/6.36    (![A:$i,B:$i]:
% 6.12/6.36     ( ( r1_tarski @ A @ B ) <=>
% 6.12/6.36       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 6.12/6.36  thf('3', plain,
% 6.12/6.36      (![X1 : $i, X3 : $i]:
% 6.12/6.36         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 6.12/6.36      inference('cnf', [status(esa)], [d3_tarski])).
% 6.12/6.36  thf('4', plain,
% 6.12/6.36      (![X1 : $i, X3 : $i]:
% 6.12/6.36         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 6.12/6.36      inference('cnf', [status(esa)], [d3_tarski])).
% 6.12/6.36  thf('5', plain,
% 6.12/6.36      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 6.12/6.36      inference('sup-', [status(thm)], ['3', '4'])).
% 6.12/6.36  thf('6', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 6.12/6.36      inference('simplify', [status(thm)], ['5'])).
% 6.12/6.36  thf(d1_zfmisc_1, axiom,
% 6.12/6.36    (![A:$i,B:$i]:
% 6.12/6.36     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 6.12/6.36       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 6.12/6.36  thf('7', plain,
% 6.12/6.36      (![X54 : $i, X55 : $i, X56 : $i]:
% 6.12/6.36         (~ (r1_tarski @ X54 @ X55)
% 6.12/6.36          | (r2_hidden @ X54 @ X56)
% 6.12/6.36          | ((X56) != (k1_zfmisc_1 @ X55)))),
% 6.12/6.36      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 6.12/6.36  thf('8', plain,
% 6.12/6.36      (![X54 : $i, X55 : $i]:
% 6.12/6.36         ((r2_hidden @ X54 @ (k1_zfmisc_1 @ X55)) | ~ (r1_tarski @ X54 @ X55))),
% 6.12/6.36      inference('simplify', [status(thm)], ['7'])).
% 6.12/6.36  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 6.12/6.36      inference('sup-', [status(thm)], ['6', '8'])).
% 6.12/6.36  thf(t6_boole, axiom,
% 6.12/6.36    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 6.12/6.36  thf('10', plain,
% 6.12/6.36      (![X17 : $i]: (((X17) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X17))),
% 6.12/6.36      inference('cnf', [status(esa)], [t6_boole])).
% 6.12/6.36  thf(t92_xboole_1, axiom,
% 6.12/6.36    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 6.12/6.36  thf('11', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 6.12/6.36      inference('cnf', [status(esa)], [t92_xboole_1])).
% 6.12/6.36  thf(idempotence_k2_xboole_0, axiom,
% 6.12/6.36    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 6.12/6.36  thf('12', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 6.12/6.36      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 6.12/6.36  thf(t95_xboole_1, axiom,
% 6.12/6.36    (![A:$i,B:$i]:
% 6.12/6.36     ( ( k3_xboole_0 @ A @ B ) =
% 6.12/6.36       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 6.12/6.36  thf('13', plain,
% 6.12/6.36      (![X24 : $i, X25 : $i]:
% 6.12/6.36         ((k3_xboole_0 @ X24 @ X25)
% 6.12/6.36           = (k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 6.12/6.36              (k2_xboole_0 @ X24 @ X25)))),
% 6.12/6.36      inference('cnf', [status(esa)], [t95_xboole_1])).
% 6.12/6.36  thf(t91_xboole_1, axiom,
% 6.12/6.36    (![A:$i,B:$i,C:$i]:
% 6.12/6.36     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 6.12/6.36       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 6.12/6.36  thf('14', plain,
% 6.12/6.36      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.12/6.36         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 6.12/6.36           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 6.12/6.36      inference('cnf', [status(esa)], [t91_xboole_1])).
% 6.12/6.36  thf('15', plain,
% 6.12/6.36      (![X24 : $i, X25 : $i]:
% 6.12/6.36         ((k3_xboole_0 @ X24 @ X25)
% 6.12/6.36           = (k5_xboole_0 @ X24 @ 
% 6.12/6.36              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 6.12/6.36      inference('demod', [status(thm)], ['13', '14'])).
% 6.12/6.36  thf('16', plain,
% 6.12/6.36      (![X0 : $i]:
% 6.12/6.36         ((k3_xboole_0 @ X0 @ X0)
% 6.12/6.36           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 6.12/6.36      inference('sup+', [status(thm)], ['12', '15'])).
% 6.12/6.36  thf('17', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 6.12/6.36      inference('cnf', [status(esa)], [t92_xboole_1])).
% 6.12/6.36  thf(t5_boole, axiom,
% 6.12/6.36    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 6.12/6.36  thf('18', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 6.12/6.36      inference('cnf', [status(esa)], [t5_boole])).
% 6.12/6.36  thf('19', plain,
% 6.12/6.36      (![X0 : $i, X1 : $i]:
% 6.12/6.36         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 6.12/6.36      inference('sup+', [status(thm)], ['17', '18'])).
% 6.12/6.36  thf('20', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 6.12/6.36      inference('demod', [status(thm)], ['16', '19'])).
% 6.12/6.36  thf(t100_xboole_1, axiom,
% 6.12/6.36    (![A:$i,B:$i]:
% 6.12/6.36     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 6.12/6.36  thf('21', plain,
% 6.12/6.36      (![X6 : $i, X7 : $i]:
% 6.12/6.36         ((k4_xboole_0 @ X6 @ X7)
% 6.12/6.36           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 6.12/6.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 6.12/6.36  thf('22', plain,
% 6.12/6.36      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 6.12/6.36      inference('sup+', [status(thm)], ['20', '21'])).
% 6.12/6.36  thf('23', plain, (![X23 : $i]: ((k4_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 6.12/6.36      inference('demod', [status(thm)], ['11', '22'])).
% 6.12/6.36  thf(t69_enumset1, axiom,
% 6.12/6.36    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 6.12/6.36  thf('24', plain,
% 6.12/6.36      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 6.12/6.36      inference('cnf', [status(esa)], [t69_enumset1])).
% 6.12/6.36  thf(t64_zfmisc_1, axiom,
% 6.12/6.36    (![A:$i,B:$i,C:$i]:
% 6.12/6.36     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 6.12/6.36       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 6.12/6.36  thf('25', plain,
% 6.12/6.36      (![X73 : $i, X74 : $i, X75 : $i]:
% 6.12/6.36         (((X73) != (X75))
% 6.12/6.36          | ~ (r2_hidden @ X73 @ (k4_xboole_0 @ X74 @ (k1_tarski @ X75))))),
% 6.12/6.36      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 6.12/6.36  thf('26', plain,
% 6.12/6.36      (![X74 : $i, X75 : $i]:
% 6.12/6.36         ~ (r2_hidden @ X75 @ (k4_xboole_0 @ X74 @ (k1_tarski @ X75)))),
% 6.12/6.36      inference('simplify', [status(thm)], ['25'])).
% 6.12/6.36  thf('27', plain,
% 6.12/6.36      (![X0 : $i, X1 : $i]:
% 6.12/6.36         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)))),
% 6.12/6.36      inference('sup-', [status(thm)], ['24', '26'])).
% 6.12/6.36  thf('28', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 6.12/6.36      inference('sup-', [status(thm)], ['23', '27'])).
% 6.12/6.36  thf('29', plain,
% 6.12/6.36      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 6.12/6.36      inference('sup-', [status(thm)], ['10', '28'])).
% 6.12/6.36  thf('30', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 6.12/6.36      inference('sup-', [status(thm)], ['9', '29'])).
% 6.12/6.36  thf('31', plain, ((r2_hidden @ sk_C_3 @ (k1_zfmisc_1 @ sk_A))),
% 6.12/6.36      inference('clc', [status(thm)], ['2', '30'])).
% 6.12/6.36  thf('32', plain,
% 6.12/6.36      (![X55 : $i, X56 : $i, X57 : $i]:
% 6.12/6.36         (~ (r2_hidden @ X57 @ X56)
% 6.12/6.36          | (r1_tarski @ X57 @ X55)
% 6.12/6.36          | ((X56) != (k1_zfmisc_1 @ X55)))),
% 6.12/6.36      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 6.12/6.36  thf('33', plain,
% 6.12/6.36      (![X55 : $i, X57 : $i]:
% 6.12/6.36         ((r1_tarski @ X57 @ X55) | ~ (r2_hidden @ X57 @ (k1_zfmisc_1 @ X55)))),
% 6.12/6.36      inference('simplify', [status(thm)], ['32'])).
% 6.12/6.36  thf('34', plain, ((r1_tarski @ sk_C_3 @ sk_A)),
% 6.12/6.36      inference('sup-', [status(thm)], ['31', '33'])).
% 6.12/6.36  thf('35', plain, ((r1_tarski @ sk_B_2 @ sk_C_3)),
% 6.12/6.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.36  thf(t1_xboole_1, axiom,
% 6.12/6.36    (![A:$i,B:$i,C:$i]:
% 6.12/6.36     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 6.12/6.36       ( r1_tarski @ A @ C ) ))).
% 6.12/6.36  thf('36', plain,
% 6.12/6.36      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.12/6.36         (~ (r1_tarski @ X8 @ X9)
% 6.12/6.36          | ~ (r1_tarski @ X9 @ X10)
% 6.12/6.36          | (r1_tarski @ X8 @ X10))),
% 6.12/6.36      inference('cnf', [status(esa)], [t1_xboole_1])).
% 6.12/6.36  thf('37', plain,
% 6.12/6.36      (![X0 : $i]: ((r1_tarski @ sk_B_2 @ X0) | ~ (r1_tarski @ sk_C_3 @ X0))),
% 6.12/6.36      inference('sup-', [status(thm)], ['35', '36'])).
% 6.12/6.36  thf('38', plain, ((r1_tarski @ sk_B_2 @ sk_A)),
% 6.12/6.36      inference('sup-', [status(thm)], ['34', '37'])).
% 6.12/6.36  thf('39', plain,
% 6.12/6.36      (![X54 : $i, X55 : $i]:
% 6.12/6.36         ((r2_hidden @ X54 @ (k1_zfmisc_1 @ X55)) | ~ (r1_tarski @ X54 @ X55))),
% 6.12/6.36      inference('simplify', [status(thm)], ['7'])).
% 6.12/6.36  thf('40', plain, ((r2_hidden @ sk_B_2 @ (k1_zfmisc_1 @ sk_A))),
% 6.12/6.36      inference('sup-', [status(thm)], ['38', '39'])).
% 6.12/6.36  thf('41', plain,
% 6.12/6.36      (![X80 : $i, X81 : $i]:
% 6.12/6.36         (~ (r2_hidden @ X80 @ X81)
% 6.12/6.36          | (m1_subset_1 @ X80 @ X81)
% 6.12/6.36          | (v1_xboole_0 @ X81))),
% 6.12/6.36      inference('cnf', [status(esa)], [d2_subset_1])).
% 6.12/6.36  thf('42', plain,
% 6.12/6.36      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 6.12/6.36        | (m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_A)))),
% 6.12/6.36      inference('sup-', [status(thm)], ['40', '41'])).
% 6.12/6.36  thf('43', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 6.12/6.36      inference('sup-', [status(thm)], ['9', '29'])).
% 6.12/6.36  thf('44', plain, ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_A))),
% 6.12/6.36      inference('clc', [status(thm)], ['42', '43'])).
% 6.12/6.36  thf('45', plain, ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ sk_A))),
% 6.12/6.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.36  thf(t31_subset_1, axiom,
% 6.12/6.36    (![A:$i,B:$i]:
% 6.12/6.36     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.12/6.36       ( ![C:$i]:
% 6.12/6.36         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.12/6.36           ( ( r1_tarski @ B @ C ) <=>
% 6.12/6.36             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 6.12/6.36  thf('46', plain,
% 6.12/6.36      (![X88 : $i, X89 : $i, X90 : $i]:
% 6.12/6.36         (~ (m1_subset_1 @ X88 @ (k1_zfmisc_1 @ X89))
% 6.12/6.36          | ~ (r1_tarski @ X90 @ X88)
% 6.12/6.36          | (r1_tarski @ (k3_subset_1 @ X89 @ X88) @ (k3_subset_1 @ X89 @ X90))
% 6.12/6.36          | ~ (m1_subset_1 @ X90 @ (k1_zfmisc_1 @ X89)))),
% 6.12/6.36      inference('cnf', [status(esa)], [t31_subset_1])).
% 6.12/6.36  thf('47', plain,
% 6.12/6.36      (![X0 : $i]:
% 6.12/6.36         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 6.12/6.36          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_3) @ 
% 6.12/6.36             (k3_subset_1 @ sk_A @ X0))
% 6.12/6.36          | ~ (r1_tarski @ X0 @ sk_C_3))),
% 6.12/6.36      inference('sup-', [status(thm)], ['45', '46'])).
% 6.12/6.36  thf('48', plain,
% 6.12/6.36      ((~ (r1_tarski @ sk_B_2 @ sk_C_3)
% 6.12/6.36        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_3) @ 
% 6.12/6.36           (k3_subset_1 @ sk_A @ sk_B_2)))),
% 6.12/6.36      inference('sup-', [status(thm)], ['44', '47'])).
% 6.12/6.36  thf('49', plain, ((r1_tarski @ sk_B_2 @ sk_C_3)),
% 6.12/6.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.36  thf('50', plain,
% 6.12/6.36      ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_3) @ 
% 6.12/6.36        (k3_subset_1 @ sk_A @ sk_B_2))),
% 6.12/6.36      inference('demod', [status(thm)], ['48', '49'])).
% 6.12/6.36  thf('51', plain, ((r1_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_C_3))),
% 6.12/6.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.36  thf('52', plain,
% 6.12/6.36      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.12/6.36         (~ (r1_tarski @ X8 @ X9)
% 6.12/6.36          | ~ (r1_tarski @ X9 @ X10)
% 6.12/6.36          | (r1_tarski @ X8 @ X10))),
% 6.12/6.36      inference('cnf', [status(esa)], [t1_xboole_1])).
% 6.12/6.36  thf('53', plain,
% 6.12/6.36      (![X0 : $i]:
% 6.12/6.36         ((r1_tarski @ sk_B_2 @ X0)
% 6.12/6.36          | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_3) @ X0))),
% 6.12/6.36      inference('sup-', [status(thm)], ['51', '52'])).
% 6.12/6.36  thf('54', plain, ((r1_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2))),
% 6.12/6.36      inference('sup-', [status(thm)], ['50', '53'])).
% 6.12/6.36  thf(t38_subset_1, axiom,
% 6.12/6.36    (![A:$i,B:$i]:
% 6.12/6.36     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.12/6.36       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 6.12/6.36         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 6.12/6.36  thf('55', plain,
% 6.12/6.36      (![X91 : $i, X92 : $i]:
% 6.12/6.36         (~ (r1_tarski @ X92 @ (k3_subset_1 @ X91 @ X92))
% 6.12/6.36          | ((X92) = (k1_subset_1 @ X91))
% 6.12/6.36          | ~ (m1_subset_1 @ X92 @ (k1_zfmisc_1 @ X91)))),
% 6.12/6.36      inference('cnf', [status(esa)], [t38_subset_1])).
% 6.12/6.36  thf('56', plain,
% 6.12/6.36      ((~ (m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_A))
% 6.12/6.36        | ((sk_B_2) = (k1_subset_1 @ sk_A)))),
% 6.12/6.36      inference('sup-', [status(thm)], ['54', '55'])).
% 6.12/6.36  thf('57', plain, ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_A))),
% 6.12/6.36      inference('clc', [status(thm)], ['42', '43'])).
% 6.12/6.36  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 6.12/6.36  thf('58', plain, (![X83 : $i]: ((k1_subset_1 @ X83) = (k1_xboole_0))),
% 6.12/6.36      inference('cnf', [status(esa)], [d3_subset_1])).
% 6.12/6.36  thf('59', plain, (((sk_B_2) = (k1_xboole_0))),
% 6.12/6.36      inference('demod', [status(thm)], ['56', '57', '58'])).
% 6.12/6.36  thf('60', plain, (((sk_B_2) != (k1_xboole_0))),
% 6.12/6.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.12/6.36  thf('61', plain, ($false),
% 6.12/6.36      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 6.12/6.36  
% 6.12/6.36  % SZS output end Refutation
% 6.12/6.36  
% 6.12/6.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
