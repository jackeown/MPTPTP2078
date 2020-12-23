%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8m45P52AuG

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:49 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 180 expanded)
%              Number of leaves         :   32 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  621 (1487 expanded)
%              Number of equality atoms :   59 ( 129 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X29: $i,X30: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X33 @ ( k3_subset_1 @ X33 @ X32 ) )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k4_subset_1 @ X35 @ X34 @ X36 )
        = ( k2_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['25','40'])).

thf('42',plain,(
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

thf('43',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('45',plain,(
    ! [X31: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('46',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('47',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( r1_tarski @ X21 @ X19 )
      | ( X20
       != ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('48',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_tarski @ X21 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['46','48'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('51',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['41','51'])).

thf('53',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['24','52'])).

thf('54',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('55',plain,(
    ! [X26: $i] :
      ( ( k2_subset_1 @ X26 )
      = X26 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('56',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('58',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8m45P52AuG
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:04:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.91/1.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.12  % Solved by: fo/fo7.sh
% 0.91/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.12  % done 1797 iterations in 0.670s
% 0.91/1.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.12  % SZS output start Refutation
% 0.91/1.12  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.12  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.12  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.12  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.91/1.12  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.91/1.12  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.91/1.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.12  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.91/1.12  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.91/1.12  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.91/1.12  thf(t25_subset_1, conjecture,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.12       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.91/1.12         ( k2_subset_1 @ A ) ) ))).
% 0.91/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.12    (~( ![A:$i,B:$i]:
% 0.91/1.12        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.12          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.91/1.12            ( k2_subset_1 @ A ) ) ) )),
% 0.91/1.12    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.91/1.12  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(dt_k3_subset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.12       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.91/1.12  thf('1', plain,
% 0.91/1.12      (![X29 : $i, X30 : $i]:
% 0.91/1.12         ((m1_subset_1 @ (k3_subset_1 @ X29 @ X30) @ (k1_zfmisc_1 @ X29))
% 0.91/1.12          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 0.91/1.12      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.91/1.12  thf('2', plain,
% 0.91/1.12      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['0', '1'])).
% 0.91/1.12  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(involutiveness_k3_subset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.12       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.91/1.12  thf('4', plain,
% 0.91/1.12      (![X32 : $i, X33 : $i]:
% 0.91/1.12         (((k3_subset_1 @ X33 @ (k3_subset_1 @ X33 @ X32)) = (X32))
% 0.91/1.12          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 0.91/1.12      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.91/1.12  thf('5', plain,
% 0.91/1.12      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.91/1.12      inference('sup-', [status(thm)], ['3', '4'])).
% 0.91/1.12  thf('6', plain,
% 0.91/1.12      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['0', '1'])).
% 0.91/1.12  thf(d5_subset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.12       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.91/1.12  thf('7', plain,
% 0.91/1.12      (![X27 : $i, X28 : $i]:
% 0.91/1.12         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 0.91/1.12          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.91/1.12      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.91/1.12  thf('8', plain,
% 0.91/1.12      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.91/1.12         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['6', '7'])).
% 0.91/1.12  thf('9', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('10', plain,
% 0.91/1.12      (![X27 : $i, X28 : $i]:
% 0.91/1.12         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 0.91/1.12          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.91/1.12      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.91/1.12  thf('11', plain,
% 0.91/1.12      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.91/1.12      inference('sup-', [status(thm)], ['9', '10'])).
% 0.91/1.12  thf(t48_xboole_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.91/1.12  thf('12', plain,
% 0.91/1.12      (![X14 : $i, X15 : $i]:
% 0.91/1.12         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.91/1.12           = (k3_xboole_0 @ X14 @ X15))),
% 0.91/1.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.12  thf('13', plain,
% 0.91/1.12      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.91/1.12         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.91/1.12      inference('sup+', [status(thm)], ['11', '12'])).
% 0.91/1.12  thf('14', plain,
% 0.91/1.12      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.91/1.12         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.91/1.12      inference('sup+', [status(thm)], ['8', '13'])).
% 0.91/1.12  thf('15', plain, (((sk_B) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.91/1.12      inference('sup+', [status(thm)], ['5', '14'])).
% 0.91/1.12  thf(t100_xboole_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.91/1.12  thf('16', plain,
% 0.91/1.12      (![X2 : $i, X3 : $i]:
% 0.91/1.12         ((k4_xboole_0 @ X2 @ X3)
% 0.91/1.12           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.91/1.12      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.12  thf('17', plain,
% 0.91/1.12      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.91/1.12      inference('sup+', [status(thm)], ['15', '16'])).
% 0.91/1.12  thf('18', plain,
% 0.91/1.12      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.91/1.12      inference('sup-', [status(thm)], ['9', '10'])).
% 0.91/1.12  thf('19', plain,
% 0.91/1.12      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.91/1.12      inference('sup+', [status(thm)], ['17', '18'])).
% 0.91/1.12  thf('20', plain,
% 0.91/1.12      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.91/1.12      inference('demod', [status(thm)], ['2', '19'])).
% 0.91/1.12  thf('21', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(redefinition_k4_subset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.91/1.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.91/1.12       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.91/1.12  thf('22', plain,
% 0.91/1.12      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.91/1.12          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35))
% 0.91/1.12          | ((k4_subset_1 @ X35 @ X34 @ X36) = (k2_xboole_0 @ X34 @ X36)))),
% 0.91/1.12      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.91/1.12  thf('23', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.91/1.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['21', '22'])).
% 0.91/1.12  thf('24', plain,
% 0.91/1.12      (((k4_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.91/1.12         = (k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['20', '23'])).
% 0.91/1.12  thf('25', plain,
% 0.91/1.12      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.91/1.12      inference('sup+', [status(thm)], ['15', '16'])).
% 0.91/1.12  thf(t22_xboole_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.91/1.12  thf('26', plain,
% 0.91/1.12      (![X6 : $i, X7 : $i]:
% 0.91/1.12         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)) = (X6))),
% 0.91/1.12      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.91/1.12  thf(t46_xboole_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.91/1.12  thf('27', plain,
% 0.91/1.12      (![X12 : $i, X13 : $i]:
% 0.91/1.12         ((k4_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (k1_xboole_0))),
% 0.91/1.12      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.91/1.12  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.12      inference('sup+', [status(thm)], ['26', '27'])).
% 0.91/1.12  thf('29', plain,
% 0.91/1.12      (![X14 : $i, X15 : $i]:
% 0.91/1.12         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.91/1.12           = (k3_xboole_0 @ X14 @ X15))),
% 0.91/1.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.12  thf('30', plain,
% 0.91/1.12      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.91/1.12      inference('sup+', [status(thm)], ['28', '29'])).
% 0.91/1.12  thf(t3_boole, axiom,
% 0.91/1.12    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.91/1.12  thf('31', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.91/1.12      inference('cnf', [status(esa)], [t3_boole])).
% 0.91/1.12  thf('32', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.91/1.12      inference('demod', [status(thm)], ['30', '31'])).
% 0.91/1.12  thf('33', plain,
% 0.91/1.12      (![X6 : $i, X7 : $i]:
% 0.91/1.12         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)) = (X6))),
% 0.91/1.12      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.91/1.12  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.91/1.12      inference('sup+', [status(thm)], ['32', '33'])).
% 0.91/1.12  thf(t41_xboole_1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.91/1.12       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.91/1.12  thf('35', plain,
% 0.91/1.12      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.91/1.12         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.91/1.12           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.91/1.12      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.91/1.12  thf(t98_xboole_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.91/1.12  thf('36', plain,
% 0.91/1.12      (![X16 : $i, X17 : $i]:
% 0.91/1.12         ((k2_xboole_0 @ X16 @ X17)
% 0.91/1.12           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.91/1.12      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.91/1.12  thf('37', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.12         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 0.91/1.12           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.91/1.12      inference('sup+', [status(thm)], ['35', '36'])).
% 0.91/1.12  thf('38', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.91/1.12           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.91/1.12      inference('sup+', [status(thm)], ['34', '37'])).
% 0.91/1.12  thf('39', plain,
% 0.91/1.12      (![X16 : $i, X17 : $i]:
% 0.91/1.12         ((k2_xboole_0 @ X16 @ X17)
% 0.91/1.12           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.91/1.12      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.91/1.12  thf('40', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.91/1.12           = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.12      inference('demod', [status(thm)], ['38', '39'])).
% 0.91/1.12  thf('41', plain,
% 0.91/1.12      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.91/1.12         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.91/1.12      inference('sup+', [status(thm)], ['25', '40'])).
% 0.91/1.12  thf('42', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(d2_subset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( ( v1_xboole_0 @ A ) =>
% 0.91/1.12         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.91/1.12       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.91/1.12         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.91/1.12  thf('43', plain,
% 0.91/1.12      (![X23 : $i, X24 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X23 @ X24)
% 0.91/1.12          | (r2_hidden @ X23 @ X24)
% 0.91/1.12          | (v1_xboole_0 @ X24))),
% 0.91/1.12      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.91/1.12  thf('44', plain,
% 0.91/1.12      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.91/1.12        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['42', '43'])).
% 0.91/1.12  thf(fc1_subset_1, axiom,
% 0.91/1.12    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.91/1.12  thf('45', plain, (![X31 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 0.91/1.12      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.91/1.12  thf('46', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.91/1.12      inference('clc', [status(thm)], ['44', '45'])).
% 0.91/1.12  thf(d1_zfmisc_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.91/1.12       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.91/1.12  thf('47', plain,
% 0.91/1.12      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.91/1.12         (~ (r2_hidden @ X21 @ X20)
% 0.91/1.12          | (r1_tarski @ X21 @ X19)
% 0.91/1.12          | ((X20) != (k1_zfmisc_1 @ X19)))),
% 0.91/1.12      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.91/1.12  thf('48', plain,
% 0.91/1.12      (![X19 : $i, X21 : $i]:
% 0.91/1.12         ((r1_tarski @ X21 @ X19) | ~ (r2_hidden @ X21 @ (k1_zfmisc_1 @ X19)))),
% 0.91/1.12      inference('simplify', [status(thm)], ['47'])).
% 0.91/1.12  thf('49', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.91/1.12      inference('sup-', [status(thm)], ['46', '48'])).
% 0.91/1.12  thf(t12_xboole_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.91/1.12  thf('50', plain,
% 0.91/1.12      (![X4 : $i, X5 : $i]:
% 0.91/1.12         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.91/1.12      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.91/1.12  thf('51', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['49', '50'])).
% 0.91/1.12  thf('52', plain,
% 0.91/1.12      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.91/1.12      inference('demod', [status(thm)], ['41', '51'])).
% 0.91/1.12  thf('53', plain,
% 0.91/1.12      (((k4_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.91/1.12      inference('demod', [status(thm)], ['24', '52'])).
% 0.91/1.12  thf('54', plain,
% 0.91/1.12      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.91/1.12         != (k2_subset_1 @ sk_A))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.91/1.12  thf('55', plain, (![X26 : $i]: ((k2_subset_1 @ X26) = (X26))),
% 0.91/1.12      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.91/1.12  thf('56', plain,
% 0.91/1.12      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.91/1.12      inference('demod', [status(thm)], ['54', '55'])).
% 0.91/1.12  thf('57', plain,
% 0.91/1.12      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.91/1.12      inference('sup+', [status(thm)], ['17', '18'])).
% 0.91/1.12  thf('58', plain,
% 0.91/1.12      (((k4_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.91/1.12      inference('demod', [status(thm)], ['56', '57'])).
% 0.91/1.12  thf('59', plain, ($false),
% 0.91/1.12      inference('simplify_reflect-', [status(thm)], ['53', '58'])).
% 0.91/1.12  
% 0.91/1.12  % SZS output end Refutation
% 0.91/1.12  
% 0.91/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
