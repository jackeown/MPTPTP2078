%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Kq1Ip5R7fL

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:52 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 128 expanded)
%              Number of leaves         :   25 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  634 (1119 expanded)
%              Number of equality atoms :   27 (  39 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_subset_1 @ X21 @ X22 )
        = ( k4_xboole_0 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k4_subset_1 @ X29 @ X28 @ X30 )
        = ( k2_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ X19 )
      | ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('15',plain,(
    ! [X25: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('16',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( r1_tarski @ X16 @ X14 )
      | ( X15
       != ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('18',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ X19 )
      | ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X25: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('24',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('26',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('31',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ( X15
       != ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ( m1_subset_1 @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X25: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('38',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_subset_1 @ X21 @ X22 )
        = ( k4_xboole_0 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('40',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','11','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('43',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X27 @ ( k3_subset_1 @ X27 @ X26 ) )
        = X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('44',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('46',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('49',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('51',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_subset_1 @ X21 @ X22 )
        = ( k4_xboole_0 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('53',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['46','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('56',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('58',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('61',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X4 )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['54','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['41','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Kq1Ip5R7fL
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.74/1.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.74/1.98  % Solved by: fo/fo7.sh
% 1.74/1.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.74/1.98  % done 2172 iterations in 1.525s
% 1.74/1.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.74/1.98  % SZS output start Refutation
% 1.74/1.98  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.74/1.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.74/1.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.74/1.98  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.74/1.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.74/1.98  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.74/1.98  thf(sk_B_type, type, sk_B: $i).
% 1.74/1.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.74/1.98  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.74/1.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.74/1.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.74/1.98  thf(sk_A_type, type, sk_A: $i).
% 1.74/1.98  thf(t41_subset_1, conjecture,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.74/1.98       ( ![C:$i]:
% 1.74/1.98         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.74/1.98           ( r1_tarski @
% 1.74/1.98             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 1.74/1.98             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 1.74/1.98  thf(zf_stmt_0, negated_conjecture,
% 1.74/1.98    (~( ![A:$i,B:$i]:
% 1.74/1.98        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.74/1.98          ( ![C:$i]:
% 1.74/1.98            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.74/1.98              ( r1_tarski @
% 1.74/1.98                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 1.74/1.98                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 1.74/1.98    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 1.74/1.98  thf('0', plain,
% 1.74/1.98      (~ (r1_tarski @ 
% 1.74/1.98          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 1.74/1.98          (k3_subset_1 @ sk_A @ sk_B))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(d5_subset_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.74/1.98       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.74/1.98  thf('2', plain,
% 1.74/1.98      (![X21 : $i, X22 : $i]:
% 1.74/1.98         (((k3_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))
% 1.74/1.98          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 1.74/1.98      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.74/1.98  thf('3', plain,
% 1.74/1.98      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.74/1.98      inference('sup-', [status(thm)], ['1', '2'])).
% 1.74/1.98  thf('4', plain,
% 1.74/1.98      (~ (r1_tarski @ 
% 1.74/1.98          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 1.74/1.98          (k4_xboole_0 @ sk_A @ sk_B))),
% 1.74/1.98      inference('demod', [status(thm)], ['0', '3'])).
% 1.74/1.98  thf('5', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('6', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(redefinition_k4_subset_1, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.74/1.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.74/1.98       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.74/1.98  thf('7', plain,
% 1.74/1.98      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.74/1.98         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 1.74/1.98          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29))
% 1.74/1.98          | ((k4_subset_1 @ X29 @ X28 @ X30) = (k2_xboole_0 @ X28 @ X30)))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.74/1.98  thf('8', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 1.74/1.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['6', '7'])).
% 1.74/1.98  thf('9', plain,
% 1.74/1.98      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 1.74/1.98      inference('sup-', [status(thm)], ['5', '8'])).
% 1.74/1.98  thf(commutativity_k2_xboole_0, axiom,
% 1.74/1.98    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.74/1.98  thf('10', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.74/1.98      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.74/1.98  thf('11', plain,
% 1.74/1.98      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_C_1 @ sk_B))),
% 1.74/1.98      inference('demod', [status(thm)], ['9', '10'])).
% 1.74/1.98  thf('12', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(d2_subset_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( ( v1_xboole_0 @ A ) =>
% 1.74/1.98         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.74/1.98       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.74/1.98         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.74/1.98  thf('13', plain,
% 1.74/1.98      (![X18 : $i, X19 : $i]:
% 1.74/1.98         (~ (m1_subset_1 @ X18 @ X19)
% 1.74/1.98          | (r2_hidden @ X18 @ X19)
% 1.74/1.98          | (v1_xboole_0 @ X19))),
% 1.74/1.98      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.74/1.98  thf('14', plain,
% 1.74/1.98      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.74/1.98        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['12', '13'])).
% 1.74/1.98  thf(fc1_subset_1, axiom,
% 1.74/1.98    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.74/1.98  thf('15', plain, (![X25 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X25))),
% 1.74/1.98      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.74/1.98  thf('16', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.74/1.98      inference('clc', [status(thm)], ['14', '15'])).
% 1.74/1.98  thf(d1_zfmisc_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.74/1.98       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.74/1.98  thf('17', plain,
% 1.74/1.98      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.74/1.98         (~ (r2_hidden @ X16 @ X15)
% 1.74/1.98          | (r1_tarski @ X16 @ X14)
% 1.74/1.98          | ((X15) != (k1_zfmisc_1 @ X14)))),
% 1.74/1.98      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.74/1.98  thf('18', plain,
% 1.74/1.98      (![X14 : $i, X16 : $i]:
% 1.74/1.98         ((r1_tarski @ X16 @ X14) | ~ (r2_hidden @ X16 @ (k1_zfmisc_1 @ X14)))),
% 1.74/1.98      inference('simplify', [status(thm)], ['17'])).
% 1.74/1.98  thf('19', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 1.74/1.98      inference('sup-', [status(thm)], ['16', '18'])).
% 1.74/1.98  thf('20', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('21', plain,
% 1.74/1.98      (![X18 : $i, X19 : $i]:
% 1.74/1.98         (~ (m1_subset_1 @ X18 @ X19)
% 1.74/1.98          | (r2_hidden @ X18 @ X19)
% 1.74/1.98          | (v1_xboole_0 @ X19))),
% 1.74/1.98      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.74/1.98  thf('22', plain,
% 1.74/1.98      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.74/1.98        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['20', '21'])).
% 1.74/1.98  thf('23', plain, (![X25 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X25))),
% 1.74/1.98      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.74/1.98  thf('24', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.74/1.98      inference('clc', [status(thm)], ['22', '23'])).
% 1.74/1.98  thf('25', plain,
% 1.74/1.98      (![X14 : $i, X16 : $i]:
% 1.74/1.98         ((r1_tarski @ X16 @ X14) | ~ (r2_hidden @ X16 @ (k1_zfmisc_1 @ X14)))),
% 1.74/1.98      inference('simplify', [status(thm)], ['17'])).
% 1.74/1.98  thf('26', plain, ((r1_tarski @ sk_B @ sk_A)),
% 1.74/1.98      inference('sup-', [status(thm)], ['24', '25'])).
% 1.74/1.98  thf(t8_xboole_1, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.74/1.98       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.74/1.98  thf('27', plain,
% 1.74/1.98      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.74/1.98         (~ (r1_tarski @ X10 @ X11)
% 1.74/1.98          | ~ (r1_tarski @ X12 @ X11)
% 1.74/1.98          | (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 1.74/1.98      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.74/1.98  thf('28', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ sk_A)
% 1.74/1.98          | ~ (r1_tarski @ X0 @ sk_A))),
% 1.74/1.98      inference('sup-', [status(thm)], ['26', '27'])).
% 1.74/1.98  thf('29', plain, ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 1.74/1.98      inference('sup-', [status(thm)], ['19', '28'])).
% 1.74/1.98  thf('30', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.74/1.98      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.74/1.98  thf('31', plain, ((r1_tarski @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A)),
% 1.74/1.98      inference('demod', [status(thm)], ['29', '30'])).
% 1.74/1.98  thf('32', plain,
% 1.74/1.98      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.74/1.98         (~ (r1_tarski @ X13 @ X14)
% 1.74/1.98          | (r2_hidden @ X13 @ X15)
% 1.74/1.98          | ((X15) != (k1_zfmisc_1 @ X14)))),
% 1.74/1.98      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.74/1.98  thf('33', plain,
% 1.74/1.98      (![X13 : $i, X14 : $i]:
% 1.74/1.98         ((r2_hidden @ X13 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X13 @ X14))),
% 1.74/1.98      inference('simplify', [status(thm)], ['32'])).
% 1.74/1.98  thf('34', plain,
% 1.74/1.98      ((r2_hidden @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 1.74/1.98      inference('sup-', [status(thm)], ['31', '33'])).
% 1.74/1.98  thf('35', plain,
% 1.74/1.98      (![X18 : $i, X19 : $i]:
% 1.74/1.98         (~ (r2_hidden @ X18 @ X19)
% 1.74/1.98          | (m1_subset_1 @ X18 @ X19)
% 1.74/1.98          | (v1_xboole_0 @ X19))),
% 1.74/1.98      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.74/1.98  thf('36', plain,
% 1.74/1.98      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.74/1.98        | (m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['34', '35'])).
% 1.74/1.98  thf('37', plain, (![X25 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X25))),
% 1.74/1.98      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.74/1.98  thf('38', plain,
% 1.74/1.98      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 1.74/1.98      inference('clc', [status(thm)], ['36', '37'])).
% 1.74/1.98  thf('39', plain,
% 1.74/1.98      (![X21 : $i, X22 : $i]:
% 1.74/1.98         (((k3_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))
% 1.74/1.98          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 1.74/1.98      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.74/1.98  thf('40', plain,
% 1.74/1.98      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 1.74/1.98         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['38', '39'])).
% 1.74/1.98  thf('41', plain,
% 1.74/1.98      (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 1.74/1.98          (k4_xboole_0 @ sk_A @ sk_B))),
% 1.74/1.98      inference('demod', [status(thm)], ['4', '11', '40'])).
% 1.74/1.98  thf('42', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(involutiveness_k3_subset_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.74/1.98       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.74/1.98  thf('43', plain,
% 1.74/1.98      (![X26 : $i, X27 : $i]:
% 1.74/1.98         (((k3_subset_1 @ X27 @ (k3_subset_1 @ X27 @ X26)) = (X26))
% 1.74/1.98          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 1.74/1.98      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.74/1.98  thf('44', plain,
% 1.74/1.98      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 1.74/1.98      inference('sup-', [status(thm)], ['42', '43'])).
% 1.74/1.98  thf('45', plain,
% 1.74/1.98      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.74/1.98      inference('sup-', [status(thm)], ['1', '2'])).
% 1.74/1.98  thf('46', plain,
% 1.74/1.98      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 1.74/1.98      inference('demod', [status(thm)], ['44', '45'])).
% 1.74/1.98  thf('47', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(dt_k3_subset_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.74/1.98       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.74/1.98  thf('48', plain,
% 1.74/1.98      (![X23 : $i, X24 : $i]:
% 1.74/1.98         ((m1_subset_1 @ (k3_subset_1 @ X23 @ X24) @ (k1_zfmisc_1 @ X23))
% 1.74/1.98          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 1.74/1.98      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.74/1.98  thf('49', plain,
% 1.74/1.98      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 1.74/1.98      inference('sup-', [status(thm)], ['47', '48'])).
% 1.74/1.98  thf('50', plain,
% 1.74/1.98      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.74/1.98      inference('sup-', [status(thm)], ['1', '2'])).
% 1.74/1.98  thf('51', plain,
% 1.74/1.98      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 1.74/1.98      inference('demod', [status(thm)], ['49', '50'])).
% 1.74/1.98  thf('52', plain,
% 1.74/1.98      (![X21 : $i, X22 : $i]:
% 1.74/1.98         (((k3_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))
% 1.74/1.98          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 1.74/1.98      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.74/1.98  thf('53', plain,
% 1.74/1.98      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 1.74/1.98         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['51', '52'])).
% 1.74/1.98  thf('54', plain,
% 1.74/1.98      (((sk_B) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 1.74/1.98      inference('sup+', [status(thm)], ['46', '53'])).
% 1.74/1.98  thf('55', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.74/1.98      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.74/1.98  thf(t7_xboole_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.74/1.98  thf('56', plain,
% 1.74/1.98      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 1.74/1.98      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.74/1.98  thf('57', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.74/1.98      inference('sup+', [status(thm)], ['55', '56'])).
% 1.74/1.98  thf(t44_xboole_1, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.74/1.98       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.74/1.98  thf('58', plain,
% 1.74/1.98      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.74/1.98         ((r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7))
% 1.74/1.98          | ~ (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X7))),
% 1.74/1.98      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.74/1.98  thf('59', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.98         (r1_tarski @ X1 @ 
% 1.74/1.98          (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['57', '58'])).
% 1.74/1.98  thf('60', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.74/1.98      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.74/1.98  thf(t43_xboole_1, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.74/1.98       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.74/1.98  thf('61', plain,
% 1.74/1.98      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.74/1.98         ((r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X4)
% 1.74/1.98          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 1.74/1.98      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.74/1.98  thf('62', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.98         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 1.74/1.98          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 1.74/1.98      inference('sup-', [status(thm)], ['60', '61'])).
% 1.74/1.98  thf('63', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.98         (r1_tarski @ 
% 1.74/1.98          (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))) @ 
% 1.74/1.98          X0)),
% 1.74/1.98      inference('sup-', [status(thm)], ['59', '62'])).
% 1.74/1.98  thf('64', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         (r1_tarski @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)) @ 
% 1.74/1.98          (k4_xboole_0 @ sk_A @ sk_B))),
% 1.74/1.98      inference('sup+', [status(thm)], ['54', '63'])).
% 1.74/1.98  thf('65', plain, ($false), inference('demod', [status(thm)], ['41', '64'])).
% 1.74/1.98  
% 1.74/1.98  % SZS output end Refutation
% 1.74/1.98  
% 1.74/1.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
