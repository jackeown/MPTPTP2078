%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gLFUgxhG7r

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:51 EST 2020

% Result     : Theorem 4.81s
% Output     : Refutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 139 expanded)
%              Number of leaves         :   27 (  53 expanded)
%              Depth                    :   16
%              Number of atoms          :  685 (1070 expanded)
%              Number of equality atoms :   52 (  70 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k4_subset_1 @ X38 @ X37 @ X39 )
        = ( k2_xboole_0 @ X37 @ X39 ) ) ) ),
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

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ X28 )
      | ( r2_hidden @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X34: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('22',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ( r1_tarski @ X25 @ X23 )
      | ( X24
       != ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('24',plain,(
    ! [X23: $i,X25: $i] :
      ( ( r1_tarski @ X25 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('27',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A )
      = ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ sk_A )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('32',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ X28 )
      | ( r2_hidden @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X34: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('39',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X23: $i,X25: $i] :
      ( ( r1_tarski @ X25 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('41',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('43',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_A )
      = ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['34','45'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('48',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('54',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('55',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X24 )
      | ( X24
       != ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('56',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ( m1_subset_1 @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X34: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','61'])).

thf('63',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['52','62'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('64',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k4_xboole_0 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('65',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('67',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k4_xboole_0 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('71',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['65','68','71'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('73',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['8','72','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gLFUgxhG7r
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:20:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 4.81/4.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.81/4.99  % Solved by: fo/fo7.sh
% 4.81/4.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.81/4.99  % done 6849 iterations in 4.537s
% 4.81/4.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.81/4.99  % SZS output start Refutation
% 4.81/4.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.81/4.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.81/4.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.81/4.99  thf(sk_A_type, type, sk_A: $i).
% 4.81/4.99  thf(sk_B_type, type, sk_B: $i).
% 4.81/4.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.81/4.99  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.81/4.99  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 4.81/4.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.81/4.99  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 4.81/4.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.81/4.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.81/4.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.81/4.99  thf(t41_subset_1, conjecture,
% 4.81/4.99    (![A:$i,B:$i]:
% 4.81/4.99     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.81/4.99       ( ![C:$i]:
% 4.81/4.99         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 4.81/4.99           ( r1_tarski @
% 4.81/4.99             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 4.81/4.99             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 4.81/4.99  thf(zf_stmt_0, negated_conjecture,
% 4.81/4.99    (~( ![A:$i,B:$i]:
% 4.81/4.99        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.81/4.99          ( ![C:$i]:
% 4.81/4.99            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 4.81/4.99              ( r1_tarski @
% 4.81/4.99                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 4.81/4.99                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 4.81/4.99    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 4.81/4.99  thf('0', plain,
% 4.81/4.99      (~ (r1_tarski @ 
% 4.81/4.99          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 4.81/4.99          (k3_subset_1 @ sk_A @ sk_B))),
% 4.81/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.81/4.99  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 4.81/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.81/4.99  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 4.81/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.81/4.99  thf(redefinition_k4_subset_1, axiom,
% 4.81/4.99    (![A:$i,B:$i,C:$i]:
% 4.81/4.99     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 4.81/4.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 4.81/4.99       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 4.81/4.99  thf('3', plain,
% 4.81/4.99      (![X37 : $i, X38 : $i, X39 : $i]:
% 4.81/4.99         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 4.81/4.99          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38))
% 4.81/4.99          | ((k4_subset_1 @ X38 @ X37 @ X39) = (k2_xboole_0 @ X37 @ X39)))),
% 4.81/4.99      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 4.81/4.99  thf('4', plain,
% 4.81/4.99      (![X0 : $i]:
% 4.81/4.99         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 4.81/4.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 4.81/4.99      inference('sup-', [status(thm)], ['2', '3'])).
% 4.81/4.99  thf('5', plain,
% 4.81/4.99      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 4.81/4.99      inference('sup-', [status(thm)], ['1', '4'])).
% 4.81/4.99  thf(commutativity_k2_xboole_0, axiom,
% 4.81/4.99    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 4.81/4.99  thf('6', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.81/4.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.81/4.99  thf('7', plain,
% 4.81/4.99      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_C_1 @ sk_B))),
% 4.81/4.99      inference('demod', [status(thm)], ['5', '6'])).
% 4.81/4.99  thf('8', plain,
% 4.81/4.99      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 4.81/4.99          (k3_subset_1 @ sk_A @ sk_B))),
% 4.81/4.99      inference('demod', [status(thm)], ['0', '7'])).
% 4.81/4.99  thf(t41_xboole_1, axiom,
% 4.81/4.99    (![A:$i,B:$i,C:$i]:
% 4.81/4.99     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 4.81/4.99       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 4.81/4.99  thf('9', plain,
% 4.81/4.99      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.81/4.99         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 4.81/4.99           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 4.81/4.99      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.81/4.99  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.81/4.99  thf('10', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 4.81/4.99      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.81/4.99  thf(t12_xboole_1, axiom,
% 4.81/4.99    (![A:$i,B:$i]:
% 4.81/4.99     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 4.81/4.99  thf('11', plain,
% 4.81/4.99      (![X2 : $i, X3 : $i]:
% 4.81/4.99         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 4.81/4.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 4.81/4.99  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 4.81/4.99      inference('sup-', [status(thm)], ['10', '11'])).
% 4.81/4.99  thf('13', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.81/4.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.81/4.99  thf(t46_xboole_1, axiom,
% 4.81/4.99    (![A:$i,B:$i]:
% 4.81/4.99     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 4.81/4.99  thf('14', plain,
% 4.81/4.99      (![X18 : $i, X19 : $i]:
% 4.81/4.99         ((k4_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19)) = (k1_xboole_0))),
% 4.81/4.99      inference('cnf', [status(esa)], [t46_xboole_1])).
% 4.81/4.99  thf('15', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i]:
% 4.81/4.99         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 4.81/4.99      inference('sup+', [status(thm)], ['13', '14'])).
% 4.81/4.99  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 4.81/4.99      inference('sup+', [status(thm)], ['12', '15'])).
% 4.81/4.99  thf('17', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i]:
% 4.81/4.99         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 4.81/4.99           = (k1_xboole_0))),
% 4.81/4.99      inference('sup+', [status(thm)], ['9', '16'])).
% 4.81/4.99  thf('18', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 4.81/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.81/4.99  thf(d2_subset_1, axiom,
% 4.81/4.99    (![A:$i,B:$i]:
% 4.81/4.99     ( ( ( v1_xboole_0 @ A ) =>
% 4.81/4.99         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 4.81/4.99       ( ( ~( v1_xboole_0 @ A ) ) =>
% 4.81/4.99         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 4.81/4.99  thf('19', plain,
% 4.81/4.99      (![X27 : $i, X28 : $i]:
% 4.81/4.99         (~ (m1_subset_1 @ X27 @ X28)
% 4.81/4.99          | (r2_hidden @ X27 @ X28)
% 4.81/4.99          | (v1_xboole_0 @ X28))),
% 4.81/4.99      inference('cnf', [status(esa)], [d2_subset_1])).
% 4.81/4.99  thf('20', plain,
% 4.81/4.99      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 4.81/4.99        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 4.81/4.99      inference('sup-', [status(thm)], ['18', '19'])).
% 4.81/4.99  thf(fc1_subset_1, axiom,
% 4.81/4.99    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 4.81/4.99  thf('21', plain, (![X34 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X34))),
% 4.81/4.99      inference('cnf', [status(esa)], [fc1_subset_1])).
% 4.81/4.99  thf('22', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 4.81/4.99      inference('clc', [status(thm)], ['20', '21'])).
% 4.81/4.99  thf(d1_zfmisc_1, axiom,
% 4.81/4.99    (![A:$i,B:$i]:
% 4.81/4.99     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 4.81/4.99       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 4.81/4.99  thf('23', plain,
% 4.81/4.99      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.81/4.99         (~ (r2_hidden @ X25 @ X24)
% 4.81/4.99          | (r1_tarski @ X25 @ X23)
% 4.81/4.99          | ((X24) != (k1_zfmisc_1 @ X23)))),
% 4.81/4.99      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 4.81/4.99  thf('24', plain,
% 4.81/4.99      (![X23 : $i, X25 : $i]:
% 4.81/4.99         ((r1_tarski @ X25 @ X23) | ~ (r2_hidden @ X25 @ (k1_zfmisc_1 @ X23)))),
% 4.81/4.99      inference('simplify', [status(thm)], ['23'])).
% 4.81/4.99  thf('25', plain, ((r1_tarski @ sk_B @ sk_A)),
% 4.81/4.99      inference('sup-', [status(thm)], ['22', '24'])).
% 4.81/4.99  thf('26', plain,
% 4.81/4.99      (![X2 : $i, X3 : $i]:
% 4.81/4.99         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 4.81/4.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 4.81/4.99  thf('27', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 4.81/4.99      inference('sup-', [status(thm)], ['25', '26'])).
% 4.81/4.99  thf('28', plain,
% 4.81/4.99      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.81/4.99         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 4.81/4.99           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 4.81/4.99      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.81/4.99  thf('29', plain,
% 4.81/4.99      (![X0 : $i]:
% 4.81/4.99         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)
% 4.81/4.99           = (k4_xboole_0 @ X0 @ sk_A))),
% 4.81/4.99      inference('sup+', [status(thm)], ['27', '28'])).
% 4.81/4.99  thf('30', plain,
% 4.81/4.99      (![X0 : $i]:
% 4.81/4.99         ((k4_xboole_0 @ k1_xboole_0 @ sk_A)
% 4.81/4.99           = (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ X0) @ 
% 4.81/4.99              sk_A))),
% 4.81/4.99      inference('sup+', [status(thm)], ['17', '29'])).
% 4.81/4.99  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 4.81/4.99      inference('sup-', [status(thm)], ['10', '11'])).
% 4.81/4.99  thf('32', plain,
% 4.81/4.99      (![X18 : $i, X19 : $i]:
% 4.81/4.99         ((k4_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19)) = (k1_xboole_0))),
% 4.81/4.99      inference('cnf', [status(esa)], [t46_xboole_1])).
% 4.81/4.99  thf('33', plain,
% 4.81/4.99      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.81/4.99      inference('sup+', [status(thm)], ['31', '32'])).
% 4.81/4.99  thf('34', plain,
% 4.81/4.99      (![X0 : $i]:
% 4.81/4.99         ((k1_xboole_0)
% 4.81/4.99           = (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ X0) @ 
% 4.81/4.99              sk_A))),
% 4.81/4.99      inference('demod', [status(thm)], ['30', '33'])).
% 4.81/4.99  thf('35', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 4.81/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.81/4.99  thf('36', plain,
% 4.81/4.99      (![X27 : $i, X28 : $i]:
% 4.81/4.99         (~ (m1_subset_1 @ X27 @ X28)
% 4.81/4.99          | (r2_hidden @ X27 @ X28)
% 4.81/4.99          | (v1_xboole_0 @ X28))),
% 4.81/4.99      inference('cnf', [status(esa)], [d2_subset_1])).
% 4.81/4.99  thf('37', plain,
% 4.81/4.99      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 4.81/4.99        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 4.81/4.99      inference('sup-', [status(thm)], ['35', '36'])).
% 4.81/4.99  thf('38', plain, (![X34 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X34))),
% 4.81/4.99      inference('cnf', [status(esa)], [fc1_subset_1])).
% 4.81/4.99  thf('39', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 4.81/4.99      inference('clc', [status(thm)], ['37', '38'])).
% 4.81/4.99  thf('40', plain,
% 4.81/4.99      (![X23 : $i, X25 : $i]:
% 4.81/4.99         ((r1_tarski @ X25 @ X23) | ~ (r2_hidden @ X25 @ (k1_zfmisc_1 @ X23)))),
% 4.81/4.99      inference('simplify', [status(thm)], ['23'])).
% 4.81/4.99  thf('41', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 4.81/4.99      inference('sup-', [status(thm)], ['39', '40'])).
% 4.81/4.99  thf('42', plain,
% 4.81/4.99      (![X2 : $i, X3 : $i]:
% 4.81/4.99         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 4.81/4.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 4.81/4.99  thf('43', plain, (((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 4.81/4.99      inference('sup-', [status(thm)], ['41', '42'])).
% 4.81/4.99  thf('44', plain,
% 4.81/4.99      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.81/4.99         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 4.81/4.99           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 4.81/4.99      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.81/4.99  thf('45', plain,
% 4.81/4.99      (![X0 : $i]:
% 4.81/4.99         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_A)
% 4.81/4.99           = (k4_xboole_0 @ X0 @ sk_A))),
% 4.81/4.99      inference('sup+', [status(thm)], ['43', '44'])).
% 4.81/4.99  thf('46', plain,
% 4.81/4.99      (((k1_xboole_0) = (k4_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A))),
% 4.81/4.99      inference('sup+', [status(thm)], ['34', '45'])).
% 4.81/4.99  thf(t39_xboole_1, axiom,
% 4.81/4.99    (![A:$i,B:$i]:
% 4.81/4.99     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.81/4.99  thf('47', plain,
% 4.81/4.99      (![X10 : $i, X11 : $i]:
% 4.81/4.99         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 4.81/4.99           = (k2_xboole_0 @ X10 @ X11))),
% 4.81/4.99      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.81/4.99  thf('48', plain,
% 4.81/4.99      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 4.81/4.99         = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 4.81/4.99      inference('sup+', [status(thm)], ['46', '47'])).
% 4.81/4.99  thf('49', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 4.81/4.99      inference('sup-', [status(thm)], ['10', '11'])).
% 4.81/4.99  thf('50', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.81/4.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.81/4.99  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 4.81/4.99      inference('sup+', [status(thm)], ['49', '50'])).
% 4.81/4.99  thf('52', plain,
% 4.81/4.99      (((sk_A) = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 4.81/4.99      inference('demod', [status(thm)], ['48', '51'])).
% 4.81/4.99  thf('53', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.81/4.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.81/4.99  thf(t7_xboole_1, axiom,
% 4.81/4.99    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 4.81/4.99  thf('54', plain,
% 4.81/4.99      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 4.81/4.99      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.81/4.99  thf('55', plain,
% 4.81/4.99      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.81/4.99         (~ (r1_tarski @ X22 @ X23)
% 4.81/4.99          | (r2_hidden @ X22 @ X24)
% 4.81/4.99          | ((X24) != (k1_zfmisc_1 @ X23)))),
% 4.81/4.99      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 4.81/4.99  thf('56', plain,
% 4.81/4.99      (![X22 : $i, X23 : $i]:
% 4.81/4.99         ((r2_hidden @ X22 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X22 @ X23))),
% 4.81/4.99      inference('simplify', [status(thm)], ['55'])).
% 4.81/4.99  thf('57', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i]:
% 4.81/4.99         (r2_hidden @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.81/4.99      inference('sup-', [status(thm)], ['54', '56'])).
% 4.81/4.99  thf('58', plain,
% 4.81/4.99      (![X27 : $i, X28 : $i]:
% 4.81/4.99         (~ (r2_hidden @ X27 @ X28)
% 4.81/4.99          | (m1_subset_1 @ X27 @ X28)
% 4.81/4.99          | (v1_xboole_0 @ X28))),
% 4.81/4.99      inference('cnf', [status(esa)], [d2_subset_1])).
% 4.81/4.99  thf('59', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i]:
% 4.81/4.99         ((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 4.81/4.99          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 4.81/4.99      inference('sup-', [status(thm)], ['57', '58'])).
% 4.81/4.99  thf('60', plain, (![X34 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X34))),
% 4.81/4.99      inference('cnf', [status(esa)], [fc1_subset_1])).
% 4.81/4.99  thf('61', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i]:
% 4.81/4.99         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.81/4.99      inference('clc', [status(thm)], ['59', '60'])).
% 4.81/4.99  thf('62', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i]:
% 4.81/4.99         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.81/4.99      inference('sup+', [status(thm)], ['53', '61'])).
% 4.81/4.99  thf('63', plain,
% 4.81/4.99      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 4.81/4.99      inference('sup+', [status(thm)], ['52', '62'])).
% 4.81/4.99  thf(d5_subset_1, axiom,
% 4.81/4.99    (![A:$i,B:$i]:
% 4.81/4.99     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.81/4.99       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 4.81/4.99  thf('64', plain,
% 4.81/4.99      (![X30 : $i, X31 : $i]:
% 4.81/4.99         (((k3_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))
% 4.81/4.99          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 4.81/4.99      inference('cnf', [status(esa)], [d5_subset_1])).
% 4.81/4.99  thf('65', plain,
% 4.81/4.99      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 4.81/4.99         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 4.81/4.99      inference('sup-', [status(thm)], ['63', '64'])).
% 4.81/4.99  thf('66', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.81/4.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.81/4.99  thf('67', plain,
% 4.81/4.99      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.81/4.99         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 4.81/4.99           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 4.81/4.99      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.81/4.99  thf('68', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.81/4.99         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 4.81/4.99           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.81/4.99      inference('sup+', [status(thm)], ['66', '67'])).
% 4.81/4.99  thf('69', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 4.81/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.81/4.99  thf('70', plain,
% 4.81/4.99      (![X30 : $i, X31 : $i]:
% 4.81/4.99         (((k3_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))
% 4.81/4.99          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 4.81/4.99      inference('cnf', [status(esa)], [d5_subset_1])).
% 4.81/4.99  thf('71', plain,
% 4.81/4.99      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 4.81/4.99      inference('sup-', [status(thm)], ['69', '70'])).
% 4.81/4.99  thf('72', plain,
% 4.81/4.99      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 4.81/4.99         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1))),
% 4.81/4.99      inference('demod', [status(thm)], ['65', '68', '71'])).
% 4.81/4.99  thf(t36_xboole_1, axiom,
% 4.81/4.99    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 4.81/4.99  thf('73', plain,
% 4.81/4.99      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 4.81/4.99      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.81/4.99  thf('74', plain, ($false),
% 4.81/4.99      inference('demod', [status(thm)], ['8', '72', '73'])).
% 4.81/4.99  
% 4.81/4.99  % SZS output end Refutation
% 4.81/4.99  
% 4.81/5.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
