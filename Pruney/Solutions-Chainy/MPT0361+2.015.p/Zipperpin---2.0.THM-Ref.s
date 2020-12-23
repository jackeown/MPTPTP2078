%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qvolz6AOcR

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:52 EST 2020

% Result     : Theorem 6.78s
% Output     : Refutation 6.78s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 205 expanded)
%              Number of leaves         :   27 (  74 expanded)
%              Depth                    :   21
%              Number of atoms          :  880 (1664 expanded)
%              Number of equality atoms :   66 ( 119 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t41_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k4_subset_1 @ X29 @ X28 @ X30 )
        = ( k2_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('13',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference('sup+',[status(thm)],['11','12'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ( X17
       != ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( m1_subset_1 @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X25: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('20',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('22',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('24',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X27 @ ( k3_subset_1 @ X27 @ X26 ) )
        = X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('25',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('34',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','40'])).

thf('42',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['26','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('44',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('47',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('49',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('52',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('54',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( m1_subset_1 @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X25: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('58',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('60',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X27 @ ( k3_subset_1 @ X27 @ X26 ) )
        = X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('63',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','40'])).

thf('66',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('68',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['49','68'])).

thf('70',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('73',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('76',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['69','78'])).

thf('80',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ sk_B ) @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A ),
    inference('sup+',[status(thm)],['44','81'])).

thf('83',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('84',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( m1_subset_1 @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X25: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('88',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('90',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('92',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('95',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['90','93','94'])).

thf('96',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['8','95','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qvolz6AOcR
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.78/7.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.78/7.00  % Solved by: fo/fo7.sh
% 6.78/7.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.78/7.00  % done 7762 iterations in 6.550s
% 6.78/7.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.78/7.00  % SZS output start Refutation
% 6.78/7.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.78/7.00  thf(sk_B_type, type, sk_B: $i).
% 6.78/7.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.78/7.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.78/7.00  thf(sk_A_type, type, sk_A: $i).
% 6.78/7.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.78/7.00  thf(sk_C_1_type, type, sk_C_1: $i).
% 6.78/7.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.78/7.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.78/7.00  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.78/7.00  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 6.78/7.00  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 6.78/7.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.78/7.00  thf(t41_subset_1, conjecture,
% 6.78/7.00    (![A:$i,B:$i]:
% 6.78/7.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.78/7.00       ( ![C:$i]:
% 6.78/7.00         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.78/7.00           ( r1_tarski @
% 6.78/7.00             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 6.78/7.00             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 6.78/7.00  thf(zf_stmt_0, negated_conjecture,
% 6.78/7.00    (~( ![A:$i,B:$i]:
% 6.78/7.00        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.78/7.00          ( ![C:$i]:
% 6.78/7.00            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.78/7.00              ( r1_tarski @
% 6.78/7.00                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 6.78/7.00                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 6.78/7.00    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 6.78/7.00  thf('0', plain,
% 6.78/7.00      (~ (r1_tarski @ 
% 6.78/7.00          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 6.78/7.00          (k3_subset_1 @ sk_A @ sk_B))),
% 6.78/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.78/7.00  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 6.78/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.78/7.00  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 6.78/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.78/7.00  thf(redefinition_k4_subset_1, axiom,
% 6.78/7.00    (![A:$i,B:$i,C:$i]:
% 6.78/7.00     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 6.78/7.00         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 6.78/7.00       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 6.78/7.00  thf('3', plain,
% 6.78/7.00      (![X28 : $i, X29 : $i, X30 : $i]:
% 6.78/7.00         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 6.78/7.00          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29))
% 6.78/7.00          | ((k4_subset_1 @ X29 @ X28 @ X30) = (k2_xboole_0 @ X28 @ X30)))),
% 6.78/7.00      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 6.78/7.00  thf('4', plain,
% 6.78/7.00      (![X0 : $i]:
% 6.78/7.00         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 6.78/7.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 6.78/7.00      inference('sup-', [status(thm)], ['2', '3'])).
% 6.78/7.00  thf('5', plain,
% 6.78/7.00      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 6.78/7.00      inference('sup-', [status(thm)], ['1', '4'])).
% 6.78/7.00  thf(commutativity_k2_xboole_0, axiom,
% 6.78/7.00    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 6.78/7.00  thf('6', plain,
% 6.78/7.00      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.78/7.00      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.78/7.00  thf('7', plain,
% 6.78/7.00      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_C_1 @ sk_B))),
% 6.78/7.00      inference('demod', [status(thm)], ['5', '6'])).
% 6.78/7.00  thf('8', plain,
% 6.78/7.00      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 6.78/7.00          (k3_subset_1 @ sk_A @ sk_B))),
% 6.78/7.00      inference('demod', [status(thm)], ['0', '7'])).
% 6.78/7.00  thf('9', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 6.78/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.78/7.00  thf(d5_subset_1, axiom,
% 6.78/7.00    (![A:$i,B:$i]:
% 6.78/7.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.78/7.00       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 6.78/7.00  thf('10', plain,
% 6.78/7.00      (![X23 : $i, X24 : $i]:
% 6.78/7.00         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 6.78/7.00          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 6.78/7.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 6.78/7.00  thf('11', plain,
% 6.78/7.00      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 6.78/7.00      inference('sup-', [status(thm)], ['9', '10'])).
% 6.78/7.00  thf(t36_xboole_1, axiom,
% 6.78/7.00    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 6.78/7.00  thf('12', plain,
% 6.78/7.00      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 6.78/7.00      inference('cnf', [status(esa)], [t36_xboole_1])).
% 6.78/7.00  thf('13', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_A)),
% 6.78/7.00      inference('sup+', [status(thm)], ['11', '12'])).
% 6.78/7.00  thf(d1_zfmisc_1, axiom,
% 6.78/7.00    (![A:$i,B:$i]:
% 6.78/7.00     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 6.78/7.00       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 6.78/7.00  thf('14', plain,
% 6.78/7.00      (![X15 : $i, X16 : $i, X17 : $i]:
% 6.78/7.00         (~ (r1_tarski @ X15 @ X16)
% 6.78/7.00          | (r2_hidden @ X15 @ X17)
% 6.78/7.00          | ((X17) != (k1_zfmisc_1 @ X16)))),
% 6.78/7.00      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 6.78/7.00  thf('15', plain,
% 6.78/7.00      (![X15 : $i, X16 : $i]:
% 6.78/7.00         ((r2_hidden @ X15 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X15 @ X16))),
% 6.78/7.00      inference('simplify', [status(thm)], ['14'])).
% 6.78/7.00  thf('16', plain,
% 6.78/7.00      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 6.78/7.00      inference('sup-', [status(thm)], ['13', '15'])).
% 6.78/7.00  thf(d2_subset_1, axiom,
% 6.78/7.00    (![A:$i,B:$i]:
% 6.78/7.00     ( ( ( v1_xboole_0 @ A ) =>
% 6.78/7.00         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 6.78/7.00       ( ( ~( v1_xboole_0 @ A ) ) =>
% 6.78/7.00         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 6.78/7.00  thf('17', plain,
% 6.78/7.00      (![X20 : $i, X21 : $i]:
% 6.78/7.00         (~ (r2_hidden @ X20 @ X21)
% 6.78/7.00          | (m1_subset_1 @ X20 @ X21)
% 6.78/7.00          | (v1_xboole_0 @ X21))),
% 6.78/7.00      inference('cnf', [status(esa)], [d2_subset_1])).
% 6.78/7.00  thf('18', plain,
% 6.78/7.00      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 6.78/7.00        | (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A)))),
% 6.78/7.00      inference('sup-', [status(thm)], ['16', '17'])).
% 6.78/7.00  thf(fc1_subset_1, axiom,
% 6.78/7.00    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 6.78/7.00  thf('19', plain, (![X25 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X25))),
% 6.78/7.00      inference('cnf', [status(esa)], [fc1_subset_1])).
% 6.78/7.00  thf('20', plain,
% 6.78/7.00      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 6.78/7.00      inference('clc', [status(thm)], ['18', '19'])).
% 6.78/7.00  thf('21', plain,
% 6.78/7.00      (![X23 : $i, X24 : $i]:
% 6.78/7.00         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 6.78/7.00          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 6.78/7.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 6.78/7.00  thf('22', plain,
% 6.78/7.00      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1))
% 6.78/7.00         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 6.78/7.00      inference('sup-', [status(thm)], ['20', '21'])).
% 6.78/7.00  thf('23', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 6.78/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.78/7.00  thf(involutiveness_k3_subset_1, axiom,
% 6.78/7.00    (![A:$i,B:$i]:
% 6.78/7.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.78/7.00       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 6.78/7.00  thf('24', plain,
% 6.78/7.00      (![X26 : $i, X27 : $i]:
% 6.78/7.00         (((k3_subset_1 @ X27 @ (k3_subset_1 @ X27 @ X26)) = (X26))
% 6.78/7.00          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 6.78/7.00      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 6.78/7.00  thf('25', plain,
% 6.78/7.00      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1)) = (sk_C_1))),
% 6.78/7.00      inference('sup-', [status(thm)], ['23', '24'])).
% 6.78/7.00  thf('26', plain,
% 6.78/7.00      (((sk_C_1) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 6.78/7.00      inference('demod', [status(thm)], ['22', '25'])).
% 6.78/7.00  thf('27', plain,
% 6.78/7.00      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.78/7.00      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.78/7.00  thf(t46_xboole_1, axiom,
% 6.78/7.00    (![A:$i,B:$i]:
% 6.78/7.00     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 6.78/7.00  thf('28', plain,
% 6.78/7.00      (![X13 : $i, X14 : $i]:
% 6.78/7.00         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (k1_xboole_0))),
% 6.78/7.00      inference('cnf', [status(esa)], [t46_xboole_1])).
% 6.78/7.00  thf('29', plain,
% 6.78/7.00      (![X0 : $i, X1 : $i]:
% 6.78/7.00         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 6.78/7.00      inference('sup+', [status(thm)], ['27', '28'])).
% 6.78/7.00  thf(t41_xboole_1, axiom,
% 6.78/7.00    (![A:$i,B:$i,C:$i]:
% 6.78/7.00     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 6.78/7.00       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 6.78/7.00  thf('30', plain,
% 6.78/7.00      (![X7 : $i, X8 : $i, X9 : $i]:
% 6.78/7.00         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 6.78/7.00           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 6.78/7.00      inference('cnf', [status(esa)], [t41_xboole_1])).
% 6.78/7.00  thf('31', plain,
% 6.78/7.00      (![X0 : $i, X1 : $i]:
% 6.78/7.00         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 6.78/7.00      inference('demod', [status(thm)], ['29', '30'])).
% 6.78/7.00  thf(t39_xboole_1, axiom,
% 6.78/7.00    (![A:$i,B:$i]:
% 6.78/7.00     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 6.78/7.00  thf('32', plain,
% 6.78/7.00      (![X5 : $i, X6 : $i]:
% 6.78/7.00         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 6.78/7.00           = (k2_xboole_0 @ X5 @ X6))),
% 6.78/7.00      inference('cnf', [status(esa)], [t39_xboole_1])).
% 6.78/7.00  thf('33', plain,
% 6.78/7.00      (![X0 : $i, X1 : $i]:
% 6.78/7.00         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 6.78/7.00           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 6.78/7.00      inference('sup+', [status(thm)], ['31', '32'])).
% 6.78/7.00  thf(idempotence_k2_xboole_0, axiom,
% 6.78/7.00    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 6.78/7.00  thf('34', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 6.78/7.00      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 6.78/7.00  thf('35', plain,
% 6.78/7.00      (![X13 : $i, X14 : $i]:
% 6.78/7.00         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (k1_xboole_0))),
% 6.78/7.00      inference('cnf', [status(esa)], [t46_xboole_1])).
% 6.78/7.00  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 6.78/7.00      inference('sup+', [status(thm)], ['34', '35'])).
% 6.78/7.00  thf('37', plain,
% 6.78/7.00      (![X5 : $i, X6 : $i]:
% 6.78/7.00         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 6.78/7.00           = (k2_xboole_0 @ X5 @ X6))),
% 6.78/7.00      inference('cnf', [status(esa)], [t39_xboole_1])).
% 6.78/7.00  thf('38', plain,
% 6.78/7.00      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 6.78/7.00      inference('sup+', [status(thm)], ['36', '37'])).
% 6.78/7.00  thf('39', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 6.78/7.00      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 6.78/7.00  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 6.78/7.00      inference('demod', [status(thm)], ['38', '39'])).
% 6.78/7.00  thf('41', plain,
% 6.78/7.00      (![X0 : $i, X1 : $i]:
% 6.78/7.00         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 6.78/7.00      inference('demod', [status(thm)], ['33', '40'])).
% 6.78/7.00  thf('42', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_C_1))),
% 6.78/7.00      inference('sup+', [status(thm)], ['26', '41'])).
% 6.78/7.00  thf('43', plain,
% 6.78/7.00      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.78/7.00      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.78/7.00  thf('44', plain, (((sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 6.78/7.00      inference('demod', [status(thm)], ['42', '43'])).
% 6.78/7.00  thf('45', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 6.78/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.78/7.00  thf('46', plain,
% 6.78/7.00      (![X23 : $i, X24 : $i]:
% 6.78/7.00         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 6.78/7.00          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 6.78/7.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 6.78/7.00  thf('47', plain,
% 6.78/7.00      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 6.78/7.00      inference('sup-', [status(thm)], ['45', '46'])).
% 6.78/7.00  thf('48', plain,
% 6.78/7.00      (![X5 : $i, X6 : $i]:
% 6.78/7.00         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 6.78/7.00           = (k2_xboole_0 @ X5 @ X6))),
% 6.78/7.00      inference('cnf', [status(esa)], [t39_xboole_1])).
% 6.78/7.00  thf('49', plain,
% 6.78/7.00      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 6.78/7.00         = (k2_xboole_0 @ sk_B @ sk_A))),
% 6.78/7.00      inference('sup+', [status(thm)], ['47', '48'])).
% 6.78/7.00  thf('50', plain,
% 6.78/7.00      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 6.78/7.00      inference('sup-', [status(thm)], ['45', '46'])).
% 6.78/7.00  thf('51', plain,
% 6.78/7.00      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 6.78/7.00      inference('cnf', [status(esa)], [t36_xboole_1])).
% 6.78/7.00  thf('52', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)),
% 6.78/7.00      inference('sup+', [status(thm)], ['50', '51'])).
% 6.78/7.00  thf('53', plain,
% 6.78/7.00      (![X15 : $i, X16 : $i]:
% 6.78/7.00         ((r2_hidden @ X15 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X15 @ X16))),
% 6.78/7.00      inference('simplify', [status(thm)], ['14'])).
% 6.78/7.00  thf('54', plain,
% 6.78/7.00      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 6.78/7.00      inference('sup-', [status(thm)], ['52', '53'])).
% 6.78/7.00  thf('55', plain,
% 6.78/7.00      (![X20 : $i, X21 : $i]:
% 6.78/7.00         (~ (r2_hidden @ X20 @ X21)
% 6.78/7.00          | (m1_subset_1 @ X20 @ X21)
% 6.78/7.00          | (v1_xboole_0 @ X21))),
% 6.78/7.00      inference('cnf', [status(esa)], [d2_subset_1])).
% 6.78/7.00  thf('56', plain,
% 6.78/7.00      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 6.78/7.00        | (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 6.78/7.00      inference('sup-', [status(thm)], ['54', '55'])).
% 6.78/7.00  thf('57', plain, (![X25 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X25))),
% 6.78/7.00      inference('cnf', [status(esa)], [fc1_subset_1])).
% 6.78/7.00  thf('58', plain,
% 6.78/7.00      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 6.78/7.00      inference('clc', [status(thm)], ['56', '57'])).
% 6.78/7.00  thf('59', plain,
% 6.78/7.00      (![X23 : $i, X24 : $i]:
% 6.78/7.00         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 6.78/7.00          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 6.78/7.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 6.78/7.00  thf('60', plain,
% 6.78/7.00      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 6.78/7.00         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 6.78/7.00      inference('sup-', [status(thm)], ['58', '59'])).
% 6.78/7.00  thf('61', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 6.78/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.78/7.00  thf('62', plain,
% 6.78/7.00      (![X26 : $i, X27 : $i]:
% 6.78/7.00         (((k3_subset_1 @ X27 @ (k3_subset_1 @ X27 @ X26)) = (X26))
% 6.78/7.00          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 6.78/7.00      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 6.78/7.00  thf('63', plain,
% 6.78/7.00      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 6.78/7.00      inference('sup-', [status(thm)], ['61', '62'])).
% 6.78/7.00  thf('64', plain,
% 6.78/7.00      (((sk_B) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 6.78/7.00      inference('demod', [status(thm)], ['60', '63'])).
% 6.78/7.00  thf('65', plain,
% 6.78/7.00      (![X0 : $i, X1 : $i]:
% 6.78/7.00         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 6.78/7.00      inference('demod', [status(thm)], ['33', '40'])).
% 6.78/7.00  thf('66', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_B))),
% 6.78/7.00      inference('sup+', [status(thm)], ['64', '65'])).
% 6.78/7.00  thf('67', plain,
% 6.78/7.00      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.78/7.00      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.78/7.00  thf('68', plain, (((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 6.78/7.00      inference('demod', [status(thm)], ['66', '67'])).
% 6.78/7.00  thf('69', plain,
% 6.78/7.00      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 6.78/7.00      inference('demod', [status(thm)], ['49', '68'])).
% 6.78/7.00  thf('70', plain,
% 6.78/7.00      (![X7 : $i, X8 : $i, X9 : $i]:
% 6.78/7.00         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 6.78/7.00           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 6.78/7.00      inference('cnf', [status(esa)], [t41_xboole_1])).
% 6.78/7.00  thf('71', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 6.78/7.00      inference('sup+', [status(thm)], ['34', '35'])).
% 6.78/7.00  thf('72', plain,
% 6.78/7.00      (![X0 : $i, X1 : $i]:
% 6.78/7.00         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 6.78/7.00           = (k1_xboole_0))),
% 6.78/7.00      inference('sup+', [status(thm)], ['70', '71'])).
% 6.78/7.00  thf(t44_xboole_1, axiom,
% 6.78/7.00    (![A:$i,B:$i,C:$i]:
% 6.78/7.00     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 6.78/7.00       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 6.78/7.00  thf('73', plain,
% 6.78/7.00      (![X10 : $i, X11 : $i, X12 : $i]:
% 6.78/7.00         ((r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 6.78/7.00          | ~ (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12))),
% 6.78/7.00      inference('cnf', [status(esa)], [t44_xboole_1])).
% 6.78/7.00  thf('74', plain,
% 6.78/7.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.78/7.00         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 6.78/7.00          | (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X2) @ 
% 6.78/7.00             (k2_xboole_0 @ X1 @ X0)))),
% 6.78/7.00      inference('sup-', [status(thm)], ['72', '73'])).
% 6.78/7.00  thf('75', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 6.78/7.00      inference('sup+', [status(thm)], ['34', '35'])).
% 6.78/7.00  thf('76', plain,
% 6.78/7.00      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 6.78/7.00      inference('cnf', [status(esa)], [t36_xboole_1])).
% 6.78/7.00  thf('77', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 6.78/7.00      inference('sup+', [status(thm)], ['75', '76'])).
% 6.78/7.00  thf('78', plain,
% 6.78/7.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.78/7.00         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X2) @ 
% 6.78/7.00          (k2_xboole_0 @ X1 @ X0))),
% 6.78/7.00      inference('demod', [status(thm)], ['74', '77'])).
% 6.78/7.00  thf('79', plain,
% 6.78/7.00      (![X0 : $i]:
% 6.78/7.00         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ X0) @ sk_A)),
% 6.78/7.00      inference('sup+', [status(thm)], ['69', '78'])).
% 6.78/7.00  thf('80', plain,
% 6.78/7.00      (![X10 : $i, X11 : $i, X12 : $i]:
% 6.78/7.00         ((r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 6.78/7.00          | ~ (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12))),
% 6.78/7.00      inference('cnf', [status(esa)], [t44_xboole_1])).
% 6.78/7.00  thf('81', plain,
% 6.78/7.00      (![X0 : $i]:
% 6.78/7.00         (r1_tarski @ (k2_xboole_0 @ X0 @ sk_B) @ (k2_xboole_0 @ X0 @ sk_A))),
% 6.78/7.00      inference('sup-', [status(thm)], ['79', '80'])).
% 6.78/7.00  thf('82', plain, ((r1_tarski @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A)),
% 6.78/7.00      inference('sup+', [status(thm)], ['44', '81'])).
% 6.78/7.00  thf('83', plain,
% 6.78/7.00      (![X15 : $i, X16 : $i]:
% 6.78/7.00         ((r2_hidden @ X15 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X15 @ X16))),
% 6.78/7.00      inference('simplify', [status(thm)], ['14'])).
% 6.78/7.00  thf('84', plain,
% 6.78/7.00      ((r2_hidden @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 6.78/7.00      inference('sup-', [status(thm)], ['82', '83'])).
% 6.78/7.00  thf('85', plain,
% 6.78/7.00      (![X20 : $i, X21 : $i]:
% 6.78/7.00         (~ (r2_hidden @ X20 @ X21)
% 6.78/7.00          | (m1_subset_1 @ X20 @ X21)
% 6.78/7.00          | (v1_xboole_0 @ X21))),
% 6.78/7.00      inference('cnf', [status(esa)], [d2_subset_1])).
% 6.78/7.00  thf('86', plain,
% 6.78/7.00      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 6.78/7.00        | (m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 6.78/7.00      inference('sup-', [status(thm)], ['84', '85'])).
% 6.78/7.00  thf('87', plain, (![X25 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X25))),
% 6.78/7.00      inference('cnf', [status(esa)], [fc1_subset_1])).
% 6.78/7.00  thf('88', plain,
% 6.78/7.00      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 6.78/7.00      inference('clc', [status(thm)], ['86', '87'])).
% 6.78/7.00  thf('89', plain,
% 6.78/7.00      (![X23 : $i, X24 : $i]:
% 6.78/7.00         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 6.78/7.00          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 6.78/7.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 6.78/7.00  thf('90', plain,
% 6.78/7.00      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 6.78/7.00         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 6.78/7.00      inference('sup-', [status(thm)], ['88', '89'])).
% 6.78/7.00  thf('91', plain,
% 6.78/7.00      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.78/7.00      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.78/7.00  thf('92', plain,
% 6.78/7.00      (![X7 : $i, X8 : $i, X9 : $i]:
% 6.78/7.00         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 6.78/7.00           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 6.78/7.00      inference('cnf', [status(esa)], [t41_xboole_1])).
% 6.78/7.00  thf('93', plain,
% 6.78/7.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.78/7.00         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 6.78/7.00           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 6.78/7.00      inference('sup+', [status(thm)], ['91', '92'])).
% 6.78/7.00  thf('94', plain,
% 6.78/7.00      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 6.78/7.00      inference('sup-', [status(thm)], ['45', '46'])).
% 6.78/7.00  thf('95', plain,
% 6.78/7.00      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 6.78/7.00         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1))),
% 6.78/7.00      inference('demod', [status(thm)], ['90', '93', '94'])).
% 6.78/7.00  thf('96', plain,
% 6.78/7.00      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 6.78/7.00      inference('cnf', [status(esa)], [t36_xboole_1])).
% 6.78/7.00  thf('97', plain, ($false),
% 6.78/7.00      inference('demod', [status(thm)], ['8', '95', '96'])).
% 6.78/7.00  
% 6.78/7.00  % SZS output end Refutation
% 6.78/7.00  
% 6.78/7.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
