%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.joq5y4d8xV

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:17 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 139 expanded)
%              Number of leaves         :   32 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  616 ( 985 expanded)
%              Number of equality atoms :   51 (  81 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(t50_subset_1,conjecture,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( A != k1_xboole_0 )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ( ~ ( r2_hidden @ C @ B )
                 => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_subset_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( r1_tarski @ X24 @ ( k3_subset_1 @ X25 @ X26 ) )
      | ~ ( r1_tarski @ X26 @ ( k3_subset_1 @ X25 @ X24 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_subset_1 @ X21 @ X22 )
        = ( k4_xboole_0 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('7',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X19: $i] :
      ( ( k1_subset_1 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X23: $i] :
      ( ( k2_subset_1 @ X23 )
      = ( k3_subset_1 @ X23 @ ( k1_subset_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('12',plain,(
    ! [X20: $i] :
      ( ( k2_subset_1 @ X20 )
      = X20 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('13',plain,(
    ! [X23: $i] :
      ( X23
      = ( k3_subset_1 @ X23 @ ( k1_subset_1 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('15',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('16',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['9','14','15'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','21'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('24',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_subset_1 @ X21 @ X22 )
        = ( k4_xboole_0 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('29',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32','39'])).

thf('41',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','40'])).

thf('42',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('45',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('46',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ ( k5_xboole_0 @ X4 @ X6 ) )
      | ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ sk_C @ ( k5_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_C @ k1_xboole_0 )
    | ( r2_hidden @ sk_C @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('50',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['48','53'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('55',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('56',plain,(
    ! [X19: $i] :
      ( ( k1_subset_1 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_subset_1 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k1_subset_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X19: $i] :
      ( ( k1_subset_1 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('simplify_reflect+',[status(thm)],['59','60'])).

thf('62',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['54','61'])).

thf('63',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ ( k5_xboole_0 @ X4 @ X6 ) )
      | ( r2_hidden @ X3 @ X6 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ X0 )
      | ( r2_hidden @ sk_C @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['41','64'])).

thf('66',plain,(
    ~ ( r2_hidden @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('68',plain,(
    ~ ( r2_hidden @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(clc,[status(thm)],['65','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['0','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.joq5y4d8xV
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.06/1.31  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.31  % Solved by: fo/fo7.sh
% 1.06/1.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.31  % done 2703 iterations in 0.859s
% 1.06/1.31  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.31  % SZS output start Refutation
% 1.06/1.31  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.06/1.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.31  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.06/1.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.31  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.31  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.06/1.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.31  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.31  thf(sk_C_type, type, sk_C: $i).
% 1.06/1.31  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.06/1.31  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.06/1.31  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 1.06/1.31  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.06/1.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.31  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.31  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.06/1.31  thf(t50_subset_1, conjecture,
% 1.06/1.31    (![A:$i]:
% 1.06/1.31     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 1.06/1.31       ( ![B:$i]:
% 1.06/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.31           ( ![C:$i]:
% 1.06/1.31             ( ( m1_subset_1 @ C @ A ) =>
% 1.06/1.31               ( ( ~( r2_hidden @ C @ B ) ) =>
% 1.06/1.31                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 1.06/1.31  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.31    (~( ![A:$i]:
% 1.06/1.31        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 1.06/1.31          ( ![B:$i]:
% 1.06/1.31            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.31              ( ![C:$i]:
% 1.06/1.31                ( ( m1_subset_1 @ C @ A ) =>
% 1.06/1.31                  ( ( ~( r2_hidden @ C @ B ) ) =>
% 1.06/1.31                    ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ) )),
% 1.06/1.31    inference('cnf.neg', [status(esa)], [t50_subset_1])).
% 1.06/1.31  thf('0', plain, (~ (r2_hidden @ sk_C @ sk_B)),
% 1.06/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.31  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.06/1.31  thf('1', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 1.06/1.31      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.06/1.31  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.31  thf(t35_subset_1, axiom,
% 1.06/1.31    (![A:$i,B:$i]:
% 1.06/1.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.31       ( ![C:$i]:
% 1.06/1.31         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.31           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 1.06/1.31             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 1.06/1.31  thf('3', plain,
% 1.06/1.31      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.06/1.31         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 1.06/1.31          | (r1_tarski @ X24 @ (k3_subset_1 @ X25 @ X26))
% 1.06/1.31          | ~ (r1_tarski @ X26 @ (k3_subset_1 @ X25 @ X24))
% 1.06/1.31          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 1.06/1.31      inference('cnf', [status(esa)], [t35_subset_1])).
% 1.06/1.31  thf('4', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 1.06/1.31          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 1.06/1.31          | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ X0)))),
% 1.06/1.31      inference('sup-', [status(thm)], ['2', '3'])).
% 1.06/1.31  thf('5', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.31  thf(d5_subset_1, axiom,
% 1.06/1.31    (![A:$i,B:$i]:
% 1.06/1.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.31       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.06/1.31  thf('6', plain,
% 1.06/1.31      (![X21 : $i, X22 : $i]:
% 1.06/1.31         (((k3_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))
% 1.06/1.31          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 1.06/1.31      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.06/1.31  thf('7', plain,
% 1.06/1.31      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.06/1.31      inference('sup-', [status(thm)], ['5', '6'])).
% 1.06/1.31  thf('8', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 1.06/1.31          | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))
% 1.06/1.31          | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ X0)))),
% 1.06/1.31      inference('demod', [status(thm)], ['4', '7'])).
% 1.06/1.31  thf('9', plain,
% 1.06/1.31      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0))
% 1.06/1.31        | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))),
% 1.06/1.31      inference('sup-', [status(thm)], ['1', '8'])).
% 1.06/1.31  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 1.06/1.31  thf('10', plain, (![X19 : $i]: ((k1_subset_1 @ X19) = (k1_xboole_0))),
% 1.06/1.31      inference('cnf', [status(esa)], [d3_subset_1])).
% 1.06/1.31  thf(t22_subset_1, axiom,
% 1.06/1.31    (![A:$i]:
% 1.06/1.31     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 1.06/1.31  thf('11', plain,
% 1.06/1.31      (![X23 : $i]:
% 1.06/1.31         ((k2_subset_1 @ X23) = (k3_subset_1 @ X23 @ (k1_subset_1 @ X23)))),
% 1.06/1.31      inference('cnf', [status(esa)], [t22_subset_1])).
% 1.06/1.31  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.06/1.31  thf('12', plain, (![X20 : $i]: ((k2_subset_1 @ X20) = (X20))),
% 1.06/1.31      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.06/1.31  thf('13', plain,
% 1.06/1.31      (![X23 : $i]: ((X23) = (k3_subset_1 @ X23 @ (k1_subset_1 @ X23)))),
% 1.06/1.31      inference('demod', [status(thm)], ['11', '12'])).
% 1.06/1.31  thf('14', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 1.06/1.31      inference('sup+', [status(thm)], ['10', '13'])).
% 1.06/1.31  thf(t4_subset_1, axiom,
% 1.06/1.31    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.06/1.31  thf('15', plain,
% 1.06/1.31      (![X27 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X27))),
% 1.06/1.31      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.06/1.31  thf('16', plain, ((r1_tarski @ sk_B @ sk_A)),
% 1.06/1.31      inference('demod', [status(thm)], ['9', '14', '15'])).
% 1.06/1.31  thf(t28_xboole_1, axiom,
% 1.06/1.31    (![A:$i,B:$i]:
% 1.06/1.31     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.06/1.31  thf('17', plain,
% 1.06/1.31      (![X9 : $i, X10 : $i]:
% 1.06/1.31         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 1.06/1.31      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.06/1.31  thf('18', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 1.06/1.31      inference('sup-', [status(thm)], ['16', '17'])).
% 1.06/1.31  thf(t100_xboole_1, axiom,
% 1.06/1.31    (![A:$i,B:$i]:
% 1.06/1.31     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.06/1.31  thf('19', plain,
% 1.06/1.31      (![X7 : $i, X8 : $i]:
% 1.06/1.31         ((k4_xboole_0 @ X7 @ X8)
% 1.06/1.31           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 1.06/1.31      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.06/1.31  thf('20', plain,
% 1.06/1.31      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 1.06/1.31      inference('sup+', [status(thm)], ['18', '19'])).
% 1.06/1.31  thf(t92_xboole_1, axiom,
% 1.06/1.31    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.06/1.31  thf('21', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 1.06/1.31      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.06/1.31  thf('22', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.06/1.31      inference('demod', [status(thm)], ['20', '21'])).
% 1.06/1.31  thf(d6_xboole_0, axiom,
% 1.06/1.31    (![A:$i,B:$i]:
% 1.06/1.31     ( ( k5_xboole_0 @ A @ B ) =
% 1.06/1.31       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.06/1.31  thf('23', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]:
% 1.06/1.31         ((k5_xboole_0 @ X0 @ X1)
% 1.06/1.31           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.06/1.31      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.06/1.31  thf('24', plain,
% 1.06/1.31      (((k5_xboole_0 @ sk_A @ sk_B)
% 1.06/1.31         = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0))),
% 1.06/1.31      inference('sup+', [status(thm)], ['22', '23'])).
% 1.06/1.31  thf('25', plain,
% 1.06/1.31      (![X27 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X27))),
% 1.06/1.31      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.06/1.31  thf('26', plain,
% 1.06/1.31      (![X21 : $i, X22 : $i]:
% 1.06/1.31         (((k3_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))
% 1.06/1.31          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 1.06/1.31      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.06/1.31  thf('27', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.06/1.31      inference('sup-', [status(thm)], ['25', '26'])).
% 1.06/1.31  thf('28', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 1.06/1.31      inference('sup+', [status(thm)], ['10', '13'])).
% 1.06/1.31  thf('29', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.06/1.31      inference('sup+', [status(thm)], ['27', '28'])).
% 1.06/1.31  thf('30', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]:
% 1.06/1.31         ((k5_xboole_0 @ X0 @ X1)
% 1.06/1.31           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.06/1.31      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.06/1.31  thf('31', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 1.06/1.31           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.06/1.31      inference('sup+', [status(thm)], ['29', '30'])).
% 1.06/1.31  thf(t5_boole, axiom,
% 1.06/1.31    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.06/1.31  thf('32', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.06/1.31      inference('cnf', [status(esa)], [t5_boole])).
% 1.06/1.31  thf('33', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 1.06/1.31      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.06/1.31  thf('34', plain,
% 1.06/1.31      (![X9 : $i, X10 : $i]:
% 1.06/1.31         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 1.06/1.31      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.06/1.31  thf('35', plain,
% 1.06/1.31      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.06/1.31      inference('sup-', [status(thm)], ['33', '34'])).
% 1.06/1.31  thf('36', plain,
% 1.06/1.31      (![X7 : $i, X8 : $i]:
% 1.06/1.31         ((k4_xboole_0 @ X7 @ X8)
% 1.06/1.31           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 1.06/1.31      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.06/1.31  thf('37', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 1.06/1.31           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 1.06/1.31      inference('sup+', [status(thm)], ['35', '36'])).
% 1.06/1.31  thf('38', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.06/1.31      inference('cnf', [status(esa)], [t5_boole])).
% 1.06/1.31  thf('39', plain,
% 1.06/1.31      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.06/1.31      inference('demod', [status(thm)], ['37', '38'])).
% 1.06/1.31  thf('40', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.06/1.31      inference('demod', [status(thm)], ['31', '32', '39'])).
% 1.06/1.31  thf('41', plain,
% 1.06/1.31      (((k5_xboole_0 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.06/1.31      inference('demod', [status(thm)], ['24', '40'])).
% 1.06/1.31  thf('42', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 1.06/1.31      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.06/1.31  thf('43', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 1.06/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.31  thf(d2_subset_1, axiom,
% 1.06/1.31    (![A:$i,B:$i]:
% 1.06/1.31     ( ( ( v1_xboole_0 @ A ) =>
% 1.06/1.31         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.06/1.31       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.06/1.31         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.06/1.31  thf('44', plain,
% 1.06/1.31      (![X16 : $i, X17 : $i]:
% 1.06/1.31         (~ (m1_subset_1 @ X16 @ X17)
% 1.06/1.31          | (r2_hidden @ X16 @ X17)
% 1.06/1.31          | (v1_xboole_0 @ X17))),
% 1.06/1.31      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.06/1.31  thf('45', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ sk_A))),
% 1.06/1.31      inference('sup-', [status(thm)], ['43', '44'])).
% 1.06/1.31  thf(t1_xboole_0, axiom,
% 1.06/1.31    (![A:$i,B:$i,C:$i]:
% 1.06/1.31     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.06/1.31       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 1.06/1.31  thf('46', plain,
% 1.06/1.31      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.06/1.31         ((r2_hidden @ X3 @ (k5_xboole_0 @ X4 @ X6))
% 1.06/1.31          | (r2_hidden @ X3 @ X4)
% 1.06/1.31          | ~ (r2_hidden @ X3 @ X6))),
% 1.06/1.31      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.06/1.31  thf('47', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         ((v1_xboole_0 @ sk_A)
% 1.06/1.31          | (r2_hidden @ sk_C @ X0)
% 1.06/1.31          | (r2_hidden @ sk_C @ (k5_xboole_0 @ X0 @ sk_A)))),
% 1.06/1.31      inference('sup-', [status(thm)], ['45', '46'])).
% 1.06/1.31  thf('48', plain,
% 1.06/1.31      (((r2_hidden @ sk_C @ k1_xboole_0)
% 1.06/1.31        | (r2_hidden @ sk_C @ sk_A)
% 1.06/1.31        | (v1_xboole_0 @ sk_A))),
% 1.06/1.31      inference('sup+', [status(thm)], ['42', '47'])).
% 1.06/1.31  thf('49', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 1.06/1.31      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.06/1.31  thf('50', plain,
% 1.06/1.31      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.06/1.31         (~ (r2_hidden @ X3 @ X4)
% 1.06/1.31          | ~ (r2_hidden @ X3 @ X5)
% 1.06/1.31          | ~ (r2_hidden @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 1.06/1.31      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.06/1.31  thf('51', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]:
% 1.06/1.31         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 1.06/1.31          | ~ (r2_hidden @ X1 @ X0)
% 1.06/1.31          | ~ (r2_hidden @ X1 @ X0))),
% 1.06/1.31      inference('sup-', [status(thm)], ['49', '50'])).
% 1.06/1.31  thf('52', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]:
% 1.06/1.31         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 1.06/1.31      inference('simplify', [status(thm)], ['51'])).
% 1.06/1.31  thf('53', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.06/1.31      inference('condensation', [status(thm)], ['52'])).
% 1.06/1.31  thf('54', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ sk_A))),
% 1.06/1.31      inference('clc', [status(thm)], ['48', '53'])).
% 1.06/1.31  thf(l13_xboole_0, axiom,
% 1.06/1.31    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.06/1.31  thf('55', plain,
% 1.06/1.31      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 1.06/1.31      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.06/1.31  thf('56', plain, (![X19 : $i]: ((k1_subset_1 @ X19) = (k1_xboole_0))),
% 1.06/1.31      inference('cnf', [status(esa)], [d3_subset_1])).
% 1.06/1.31  thf('57', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]:
% 1.06/1.31         (((k1_subset_1 @ X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.06/1.31      inference('sup+', [status(thm)], ['55', '56'])).
% 1.06/1.31  thf('58', plain, (((sk_A) != (k1_xboole_0))),
% 1.06/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.31  thf('59', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         (((k1_subset_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_A))),
% 1.06/1.31      inference('sup-', [status(thm)], ['57', '58'])).
% 1.06/1.31  thf('60', plain, (![X19 : $i]: ((k1_subset_1 @ X19) = (k1_xboole_0))),
% 1.06/1.31      inference('cnf', [status(esa)], [d3_subset_1])).
% 1.06/1.31  thf('61', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.06/1.31      inference('simplify_reflect+', [status(thm)], ['59', '60'])).
% 1.06/1.31  thf('62', plain, ((r2_hidden @ sk_C @ sk_A)),
% 1.06/1.31      inference('clc', [status(thm)], ['54', '61'])).
% 1.06/1.31  thf('63', plain,
% 1.06/1.31      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.06/1.31         ((r2_hidden @ X3 @ (k5_xboole_0 @ X4 @ X6))
% 1.06/1.31          | (r2_hidden @ X3 @ X6)
% 1.06/1.31          | ~ (r2_hidden @ X3 @ X4))),
% 1.06/1.31      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.06/1.31  thf('64', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         ((r2_hidden @ sk_C @ X0)
% 1.06/1.31          | (r2_hidden @ sk_C @ (k5_xboole_0 @ sk_A @ X0)))),
% 1.06/1.31      inference('sup-', [status(thm)], ['62', '63'])).
% 1.06/1.31  thf('65', plain,
% 1.06/1.31      (((r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))
% 1.06/1.31        | (r2_hidden @ sk_C @ sk_B))),
% 1.06/1.31      inference('sup+', [status(thm)], ['41', '64'])).
% 1.06/1.31  thf('66', plain, (~ (r2_hidden @ sk_C @ (k3_subset_1 @ sk_A @ sk_B))),
% 1.06/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.31  thf('67', plain,
% 1.06/1.31      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.06/1.31      inference('sup-', [status(thm)], ['5', '6'])).
% 1.06/1.31  thf('68', plain, (~ (r2_hidden @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))),
% 1.06/1.31      inference('demod', [status(thm)], ['66', '67'])).
% 1.06/1.31  thf('69', plain, ((r2_hidden @ sk_C @ sk_B)),
% 1.06/1.31      inference('clc', [status(thm)], ['65', '68'])).
% 1.06/1.31  thf('70', plain, ($false), inference('demod', [status(thm)], ['0', '69'])).
% 1.06/1.31  
% 1.06/1.31  % SZS output end Refutation
% 1.06/1.31  
% 1.06/1.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
