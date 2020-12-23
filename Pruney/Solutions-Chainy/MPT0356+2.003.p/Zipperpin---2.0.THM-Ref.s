%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o9EoGdogkr

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:17 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 224 expanded)
%              Number of leaves         :   29 (  79 expanded)
%              Depth                    :   22
%              Number of atoms          :  699 (1665 expanded)
%              Number of equality atoms :   55 ( 113 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t35_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
             => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ X27 )
      | ( r2_hidden @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X31: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('5',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( r1_tarski @ X24 @ X22 )
      | ( X23
       != ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ X24 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ X27 )
      | ( r2_hidden @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X31: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('24',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ X24 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('26',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('37',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    r1_tarski @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['29','38'])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('41',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['39','42'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 )
      | ( r1_tarski @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','45'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('47',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('48',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('51',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('54',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('58',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('59',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('62',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('63',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61','66'])).

thf('68',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['52','57','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('70',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B )
    = ( k5_xboole_0 @ sk_C_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('72',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B )
    = sk_C_1 ),
    inference(demod,[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('78',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference('sup+',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 )
      | ( r1_tarski @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ ( k4_xboole_0 @ X0 @ sk_B ) )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    r1_tarski @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['26','82'])).

thf('84',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('85',plain,(
    r1_tarski @ sk_C_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['19','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.o9EoGdogkr
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:51:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.69  % Solved by: fo/fo7.sh
% 0.46/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.69  % done 880 iterations in 0.237s
% 0.46/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.69  % SZS output start Refutation
% 0.46/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.69  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.69  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.46/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.69  thf(t35_subset_1, conjecture,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69       ( ![C:$i]:
% 0.46/0.69         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.46/0.69             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.46/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.69    (~( ![A:$i,B:$i]:
% 0.46/0.69        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69          ( ![C:$i]:
% 0.46/0.69            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69              ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.46/0.69                ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.46/0.69    inference('cnf.neg', [status(esa)], [t35_subset_1])).
% 0.46/0.69  thf('0', plain, (~ (r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(d2_subset_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ( v1_xboole_0 @ A ) =>
% 0.46/0.69         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.46/0.69       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.69         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.69  thf('2', plain,
% 0.46/0.69      (![X26 : $i, X27 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X26 @ X27)
% 0.46/0.69          | (r2_hidden @ X26 @ X27)
% 0.46/0.69          | (v1_xboole_0 @ X27))),
% 0.46/0.69      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.69  thf('3', plain,
% 0.46/0.69      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.69        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.69  thf(fc1_subset_1, axiom,
% 0.46/0.69    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.69  thf('4', plain, (![X31 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.69  thf('5', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.69      inference('clc', [status(thm)], ['3', '4'])).
% 0.46/0.69  thf(d1_zfmisc_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.46/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.46/0.69  thf('6', plain,
% 0.46/0.69      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X24 @ X23)
% 0.46/0.69          | (r1_tarski @ X24 @ X22)
% 0.46/0.69          | ((X23) != (k1_zfmisc_1 @ X22)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.46/0.69  thf('7', plain,
% 0.46/0.69      (![X22 : $i, X24 : $i]:
% 0.46/0.69         ((r1_tarski @ X24 @ X22) | ~ (r2_hidden @ X24 @ (k1_zfmisc_1 @ X22)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.69  thf('8', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.46/0.69      inference('sup-', [status(thm)], ['5', '7'])).
% 0.46/0.69  thf(t28_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.69  thf('9', plain,
% 0.46/0.69      (![X10 : $i, X11 : $i]:
% 0.46/0.69         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.46/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.69  thf('10', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.46/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.69  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.69  thf('11', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.69  thf(t100_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.69  thf('12', plain,
% 0.46/0.69      (![X5 : $i, X6 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.69           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.69  thf('13', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.69      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.69  thf('14', plain,
% 0.46/0.69      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.69      inference('sup+', [status(thm)], ['10', '13'])).
% 0.46/0.69  thf('15', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(d5_subset_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.46/0.69  thf('16', plain,
% 0.46/0.69      (![X29 : $i, X30 : $i]:
% 0.46/0.69         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 0.46/0.69          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.69  thf('17', plain,
% 0.46/0.69      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.69      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.69  thf('18', plain,
% 0.46/0.69      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.69      inference('sup+', [status(thm)], ['14', '17'])).
% 0.46/0.69  thf('19', plain, (~ (r1_tarski @ sk_C_1 @ (k5_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['0', '18'])).
% 0.46/0.69  thf('20', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('21', plain,
% 0.46/0.69      (![X26 : $i, X27 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X26 @ X27)
% 0.46/0.69          | (r2_hidden @ X26 @ X27)
% 0.46/0.69          | (v1_xboole_0 @ X27))),
% 0.46/0.69      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.69  thf('22', plain,
% 0.46/0.69      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.69        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.69  thf('23', plain, (![X31 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 0.46/0.69      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.69  thf('24', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.69      inference('clc', [status(thm)], ['22', '23'])).
% 0.46/0.69  thf('25', plain,
% 0.46/0.69      (![X22 : $i, X24 : $i]:
% 0.46/0.69         ((r1_tarski @ X24 @ X22) | ~ (r2_hidden @ X24 @ (k1_zfmisc_1 @ X22)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.69  thf('26', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.46/0.69      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.69  thf(d10_xboole_0, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.69  thf('27', plain,
% 0.46/0.69      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.69  thf('28', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.46/0.69      inference('simplify', [status(thm)], ['27'])).
% 0.46/0.69  thf('29', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('30', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.46/0.69      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.69  thf('31', plain,
% 0.46/0.69      (![X10 : $i, X11 : $i]:
% 0.46/0.69         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.46/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.69  thf('32', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.46/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.69  thf('33', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.69      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.69  thf('34', plain,
% 0.46/0.69      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.46/0.69      inference('sup+', [status(thm)], ['32', '33'])).
% 0.46/0.69  thf('35', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('36', plain,
% 0.46/0.69      (![X29 : $i, X30 : $i]:
% 0.46/0.69         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 0.46/0.69          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.69  thf('37', plain,
% 0.46/0.69      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.46/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.69  thf('38', plain,
% 0.46/0.69      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.46/0.69      inference('sup+', [status(thm)], ['34', '37'])).
% 0.46/0.69  thf('39', plain, ((r1_tarski @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.46/0.69      inference('demod', [status(thm)], ['29', '38'])).
% 0.46/0.69  thf('40', plain,
% 0.46/0.69      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.46/0.69      inference('sup+', [status(thm)], ['32', '33'])).
% 0.46/0.69  thf(t106_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.46/0.69       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.46/0.69  thf('41', plain,
% 0.46/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.69         ((r1_xboole_0 @ X7 @ X9)
% 0.46/0.69          | ~ (r1_tarski @ X7 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.46/0.69  thf('42', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (r1_tarski @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 0.46/0.69          | (r1_xboole_0 @ X0 @ sk_C_1))),
% 0.46/0.69      inference('sup-', [status(thm)], ['40', '41'])).
% 0.46/0.69  thf('43', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.46/0.69      inference('sup-', [status(thm)], ['39', '42'])).
% 0.46/0.69  thf(t86_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.46/0.69       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.46/0.69  thf('44', plain,
% 0.46/0.69      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.69         (~ (r1_tarski @ X18 @ X19)
% 0.46/0.69          | ~ (r1_xboole_0 @ X18 @ X20)
% 0.46/0.69          | (r1_tarski @ X18 @ (k4_xboole_0 @ X19 @ X20)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.46/0.69  thf('45', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1))
% 0.46/0.69          | ~ (r1_tarski @ sk_B @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.69  thf('46', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.46/0.69      inference('sup-', [status(thm)], ['28', '45'])).
% 0.46/0.69  thf(t36_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.46/0.69  thf('47', plain,
% 0.46/0.69      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.46/0.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.46/0.69  thf('48', plain,
% 0.46/0.69      (![X2 : $i, X4 : $i]:
% 0.46/0.69         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.46/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.69  thf('49', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.46/0.69          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.69  thf('50', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.46/0.69      inference('sup-', [status(thm)], ['46', '49'])).
% 0.46/0.69  thf(t48_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.69  thf('51', plain,
% 0.46/0.69      (![X16 : $i, X17 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.46/0.69           = (k3_xboole_0 @ X16 @ X17))),
% 0.46/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.69  thf('52', plain,
% 0.46/0.69      (((k4_xboole_0 @ sk_B @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.46/0.69      inference('sup+', [status(thm)], ['50', '51'])).
% 0.46/0.69  thf('53', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.46/0.69      inference('simplify', [status(thm)], ['27'])).
% 0.46/0.69  thf('54', plain,
% 0.46/0.69      (![X10 : $i, X11 : $i]:
% 0.46/0.69         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.46/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.69  thf('55', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.69  thf('56', plain,
% 0.46/0.69      (![X5 : $i, X6 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.69           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.69  thf('57', plain,
% 0.46/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['55', '56'])).
% 0.46/0.69  thf(t3_boole, axiom,
% 0.46/0.69    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.69  thf('58', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.46/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.69  thf('59', plain,
% 0.46/0.69      (![X16 : $i, X17 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.46/0.69           = (k3_xboole_0 @ X16 @ X17))),
% 0.46/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.69  thf('60', plain,
% 0.46/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['58', '59'])).
% 0.46/0.69  thf('61', plain,
% 0.46/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['55', '56'])).
% 0.46/0.69  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.69  thf('62', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.46/0.69      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.69  thf('63', plain,
% 0.46/0.69      (![X10 : $i, X11 : $i]:
% 0.46/0.69         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.46/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.69  thf('64', plain,
% 0.46/0.69      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.69  thf('65', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.69  thf('66', plain,
% 0.46/0.69      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['64', '65'])).
% 0.46/0.69  thf('67', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.69      inference('demod', [status(thm)], ['60', '61', '66'])).
% 0.46/0.69  thf('68', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.46/0.69      inference('demod', [status(thm)], ['52', '57', '67'])).
% 0.46/0.69  thf('69', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.69      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.69  thf('70', plain,
% 0.46/0.69      (((k4_xboole_0 @ sk_C_1 @ sk_B) = (k5_xboole_0 @ sk_C_1 @ k1_xboole_0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['68', '69'])).
% 0.46/0.69  thf('71', plain,
% 0.46/0.69      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['64', '65'])).
% 0.46/0.69  thf('72', plain,
% 0.46/0.69      (![X5 : $i, X6 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.69           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.69  thf('73', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['71', '72'])).
% 0.46/0.69  thf('74', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.46/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.69  thf('75', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['73', '74'])).
% 0.46/0.69  thf('76', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B) = (sk_C_1))),
% 0.46/0.69      inference('demod', [status(thm)], ['70', '75'])).
% 0.46/0.69  thf('77', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.46/0.69      inference('simplify', [status(thm)], ['27'])).
% 0.46/0.69  thf('78', plain,
% 0.46/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.69         ((r1_xboole_0 @ X7 @ X9)
% 0.46/0.69          | ~ (r1_tarski @ X7 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.46/0.69  thf('79', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.46/0.69      inference('sup-', [status(thm)], ['77', '78'])).
% 0.46/0.69  thf('80', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.46/0.69      inference('sup+', [status(thm)], ['76', '79'])).
% 0.46/0.69  thf('81', plain,
% 0.46/0.69      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.69         (~ (r1_tarski @ X18 @ X19)
% 0.46/0.69          | ~ (r1_xboole_0 @ X18 @ X20)
% 0.46/0.69          | (r1_tarski @ X18 @ (k4_xboole_0 @ X19 @ X20)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.46/0.69  thf('82', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((r1_tarski @ sk_C_1 @ (k4_xboole_0 @ X0 @ sk_B))
% 0.46/0.69          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['80', '81'])).
% 0.46/0.69  thf('83', plain, ((r1_tarski @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.69      inference('sup-', [status(thm)], ['26', '82'])).
% 0.46/0.69  thf('84', plain,
% 0.46/0.69      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.69      inference('sup+', [status(thm)], ['10', '13'])).
% 0.46/0.69  thf('85', plain, ((r1_tarski @ sk_C_1 @ (k5_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['83', '84'])).
% 0.46/0.69  thf('86', plain, ($false), inference('demod', [status(thm)], ['19', '85'])).
% 0.46/0.69  
% 0.46/0.69  % SZS output end Refutation
% 0.46/0.69  
% 0.46/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
