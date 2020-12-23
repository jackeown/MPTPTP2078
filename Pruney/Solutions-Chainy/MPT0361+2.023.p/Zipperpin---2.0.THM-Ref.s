%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9wfzun1UAo

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:53 EST 2020

% Result     : Theorem 23.13s
% Output     : Refutation 23.13s
% Verified   : 
% Statistics : Number of formulae       :  150 (1984 expanded)
%              Number of leaves         :   25 ( 620 expanded)
%              Depth                    :   26
%              Number of atoms          : 1075 (15191 expanded)
%              Number of equality atoms :   45 ( 753 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) )
      | ( ( k4_subset_1 @ X31 @ X30 @ X32 )
        = ( k2_xboole_0 @ X30 @ X32 ) ) ) ),
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

thf('6',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X21 )
      | ( X21
       != ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ( m1_subset_1 @ X24 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X29: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_subset_1 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','23'])).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ ( k4_xboole_0 @ X10 @ X9 ) @ ( k4_xboole_0 @ X10 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k3_subset_1 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_subset_1 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','23'])).

thf('30',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k3_subset_1 @ X0 @ X0 ) ) @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k3_subset_1 @ X0 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_subset_1 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','23'])).

thf('37',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('38',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ X1 @ X1 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X2 ) ),
    inference(demod,[status(thm)],['28','41'])).

thf('43',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('48',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('51',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('52',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X3 @ X2 ) @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X3 @ X2 ) @ X1 ) @ X0 ) ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X0 @ X2 ) ) @ X1 )
      | ( r1_tarski @ ( k2_xboole_0 @ X3 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['46','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','60'])).

thf('62',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','60'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','65'])).

thf('67',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('68',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ X25 )
      | ( r2_hidden @ X24 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X29: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('72',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( r1_tarski @ X22 @ X20 )
      | ( X21
       != ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('74',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_tarski @ X22 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('77',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ X25 )
      | ( r2_hidden @ X24 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X29: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('83',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_tarski @ X22 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('85',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','87'])).

thf('89',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_A ) )
      = ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X0 @ X2 ) ) @ X1 )
      | ( r1_tarski @ ( k2_xboole_0 @ X3 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','58'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ sk_A ) @ X1 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['67','95'])).

thf('97',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('98',plain,
    ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('100',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('102',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('103',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ( m1_subset_1 @ X24 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X29: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','108'])).

thf('110',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k3_subset_1 @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['100','111'])).

thf('113',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['98','99'])).

thf('114',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('116',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ ( k4_xboole_0 @ X10 @ X9 ) @ ( k4_xboole_0 @ X10 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['114','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('121',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['118','121'])).

thf('123',plain,(
    $false ),
    inference(demod,[status(thm)],['66','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9wfzun1UAo
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 23.13/23.39  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 23.13/23.39  % Solved by: fo/fo7.sh
% 23.13/23.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 23.13/23.39  % done 21056 iterations in 22.935s
% 23.13/23.39  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 23.13/23.39  % SZS output start Refutation
% 23.13/23.39  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 23.13/23.39  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 23.13/23.39  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 23.13/23.39  thf(sk_A_type, type, sk_A: $i).
% 23.13/23.39  thf(sk_C_1_type, type, sk_C_1: $i).
% 23.13/23.39  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 23.13/23.39  thf(sk_B_type, type, sk_B: $i).
% 23.13/23.39  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 23.13/23.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 23.13/23.39  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 23.13/23.39  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 23.13/23.39  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 23.13/23.39  thf(t41_subset_1, conjecture,
% 23.13/23.39    (![A:$i,B:$i]:
% 23.13/23.39     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 23.13/23.39       ( ![C:$i]:
% 23.13/23.39         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 23.13/23.39           ( r1_tarski @
% 23.13/23.39             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 23.13/23.39             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 23.13/23.39  thf(zf_stmt_0, negated_conjecture,
% 23.13/23.39    (~( ![A:$i,B:$i]:
% 23.13/23.39        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 23.13/23.39          ( ![C:$i]:
% 23.13/23.39            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 23.13/23.39              ( r1_tarski @
% 23.13/23.39                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 23.13/23.39                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 23.13/23.39    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 23.13/23.39  thf('0', plain,
% 23.13/23.39      (~ (r1_tarski @ 
% 23.13/23.39          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 23.13/23.39          (k3_subset_1 @ sk_A @ sk_B))),
% 23.13/23.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.13/23.39  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 23.13/23.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.13/23.39  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 23.13/23.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.13/23.39  thf(redefinition_k4_subset_1, axiom,
% 23.13/23.39    (![A:$i,B:$i,C:$i]:
% 23.13/23.39     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 23.13/23.39         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 23.13/23.39       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 23.13/23.39  thf('3', plain,
% 23.13/23.39      (![X30 : $i, X31 : $i, X32 : $i]:
% 23.13/23.39         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 23.13/23.39          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31))
% 23.13/23.39          | ((k4_subset_1 @ X31 @ X30 @ X32) = (k2_xboole_0 @ X30 @ X32)))),
% 23.13/23.39      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 23.13/23.39  thf('4', plain,
% 23.13/23.39      (![X0 : $i]:
% 23.13/23.39         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 23.13/23.39          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 23.13/23.39      inference('sup-', [status(thm)], ['2', '3'])).
% 23.13/23.39  thf('5', plain,
% 23.13/23.39      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 23.13/23.39      inference('sup-', [status(thm)], ['1', '4'])).
% 23.13/23.39  thf('6', plain,
% 23.13/23.39      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)) @ 
% 23.13/23.39          (k3_subset_1 @ sk_A @ sk_B))),
% 23.13/23.39      inference('demod', [status(thm)], ['0', '5'])).
% 23.13/23.39  thf(d10_xboole_0, axiom,
% 23.13/23.39    (![A:$i,B:$i]:
% 23.13/23.39     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 23.13/23.39  thf('7', plain,
% 23.13/23.39      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 23.13/23.39      inference('cnf', [status(esa)], [d10_xboole_0])).
% 23.13/23.39  thf('8', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 23.13/23.39      inference('simplify', [status(thm)], ['7'])).
% 23.13/23.39  thf(t7_xboole_1, axiom,
% 23.13/23.39    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 23.13/23.39  thf('9', plain,
% 23.13/23.39      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 23.13/23.39      inference('cnf', [status(esa)], [t7_xboole_1])).
% 23.13/23.39  thf(t43_xboole_1, axiom,
% 23.13/23.39    (![A:$i,B:$i,C:$i]:
% 23.13/23.39     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 23.13/23.39       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 23.13/23.39  thf('10', plain,
% 23.13/23.39      (![X11 : $i, X12 : $i, X13 : $i]:
% 23.13/23.39         ((r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 23.13/23.39          | ~ (r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 23.13/23.39      inference('cnf', [status(esa)], [t43_xboole_1])).
% 23.13/23.39  thf('11', plain,
% 23.13/23.39      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 23.13/23.39      inference('sup-', [status(thm)], ['9', '10'])).
% 23.13/23.39  thf(t12_xboole_1, axiom,
% 23.13/23.39    (![A:$i,B:$i]:
% 23.13/23.39     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 23.13/23.39  thf('12', plain,
% 23.13/23.39      (![X3 : $i, X4 : $i]:
% 23.13/23.39         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 23.13/23.39      inference('cnf', [status(esa)], [t12_xboole_1])).
% 23.13/23.39  thf('13', plain,
% 23.13/23.39      (![X0 : $i, X1 : $i]:
% 23.13/23.39         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 23.13/23.39      inference('sup-', [status(thm)], ['11', '12'])).
% 23.13/23.39  thf('14', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 23.13/23.39      inference('simplify', [status(thm)], ['7'])).
% 23.13/23.39  thf(d1_zfmisc_1, axiom,
% 23.13/23.39    (![A:$i,B:$i]:
% 23.13/23.39     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 23.13/23.39       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 23.13/23.39  thf('15', plain,
% 23.13/23.39      (![X19 : $i, X20 : $i, X21 : $i]:
% 23.13/23.39         (~ (r1_tarski @ X19 @ X20)
% 23.13/23.39          | (r2_hidden @ X19 @ X21)
% 23.13/23.39          | ((X21) != (k1_zfmisc_1 @ X20)))),
% 23.13/23.39      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 23.13/23.39  thf('16', plain,
% 23.13/23.39      (![X19 : $i, X20 : $i]:
% 23.13/23.39         ((r2_hidden @ X19 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X19 @ X20))),
% 23.13/23.39      inference('simplify', [status(thm)], ['15'])).
% 23.13/23.39  thf('17', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 23.13/23.39      inference('sup-', [status(thm)], ['14', '16'])).
% 23.13/23.39  thf(d2_subset_1, axiom,
% 23.13/23.39    (![A:$i,B:$i]:
% 23.13/23.39     ( ( ( v1_xboole_0 @ A ) =>
% 23.13/23.39         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 23.13/23.39       ( ( ~( v1_xboole_0 @ A ) ) =>
% 23.13/23.39         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 23.13/23.39  thf('18', plain,
% 23.13/23.39      (![X24 : $i, X25 : $i]:
% 23.13/23.39         (~ (r2_hidden @ X24 @ X25)
% 23.13/23.39          | (m1_subset_1 @ X24 @ X25)
% 23.13/23.39          | (v1_xboole_0 @ X25))),
% 23.13/23.39      inference('cnf', [status(esa)], [d2_subset_1])).
% 23.13/23.39  thf('19', plain,
% 23.13/23.39      (![X0 : $i]:
% 23.13/23.39         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 23.13/23.39          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 23.13/23.39      inference('sup-', [status(thm)], ['17', '18'])).
% 23.13/23.39  thf(fc1_subset_1, axiom,
% 23.13/23.39    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 23.13/23.39  thf('20', plain, (![X29 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 23.13/23.39      inference('cnf', [status(esa)], [fc1_subset_1])).
% 23.13/23.39  thf('21', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 23.13/23.39      inference('clc', [status(thm)], ['19', '20'])).
% 23.13/23.39  thf(d5_subset_1, axiom,
% 23.13/23.39    (![A:$i,B:$i]:
% 23.13/23.39     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 23.13/23.39       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 23.13/23.39  thf('22', plain,
% 23.13/23.39      (![X27 : $i, X28 : $i]:
% 23.13/23.39         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 23.13/23.39          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 23.13/23.39      inference('cnf', [status(esa)], [d5_subset_1])).
% 23.13/23.39  thf('23', plain,
% 23.13/23.39      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 23.13/23.39      inference('sup-', [status(thm)], ['21', '22'])).
% 23.13/23.39  thf('24', plain,
% 23.13/23.39      (![X0 : $i, X1 : $i]:
% 23.13/23.39         ((k2_xboole_0 @ (k3_subset_1 @ X1 @ X1) @ X0) = (X0))),
% 23.13/23.39      inference('demod', [status(thm)], ['13', '23'])).
% 23.13/23.39  thf('25', plain,
% 23.13/23.39      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 23.13/23.39      inference('cnf', [status(esa)], [t7_xboole_1])).
% 23.13/23.39  thf(t34_xboole_1, axiom,
% 23.13/23.39    (![A:$i,B:$i,C:$i]:
% 23.13/23.39     ( ( r1_tarski @ A @ B ) =>
% 23.13/23.39       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 23.13/23.39  thf('26', plain,
% 23.13/23.39      (![X8 : $i, X9 : $i, X10 : $i]:
% 23.13/23.39         (~ (r1_tarski @ X8 @ X9)
% 23.13/23.39          | (r1_tarski @ (k4_xboole_0 @ X10 @ X9) @ (k4_xboole_0 @ X10 @ X8)))),
% 23.13/23.39      inference('cnf', [status(esa)], [t34_xboole_1])).
% 23.13/23.39  thf('27', plain,
% 23.13/23.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.13/23.39         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 23.13/23.39          (k4_xboole_0 @ X2 @ X1))),
% 23.13/23.39      inference('sup-', [status(thm)], ['25', '26'])).
% 23.13/23.39  thf('28', plain,
% 23.13/23.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.13/23.39         (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ 
% 23.13/23.39          (k4_xboole_0 @ X2 @ (k3_subset_1 @ X1 @ X1)))),
% 23.13/23.39      inference('sup+', [status(thm)], ['24', '27'])).
% 23.13/23.39  thf('29', plain,
% 23.13/23.39      (![X0 : $i, X1 : $i]:
% 23.13/23.39         ((k2_xboole_0 @ (k3_subset_1 @ X1 @ X1) @ X0) = (X0))),
% 23.13/23.39      inference('demod', [status(thm)], ['13', '23'])).
% 23.13/23.39  thf('30', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 23.13/23.39      inference('simplify', [status(thm)], ['7'])).
% 23.13/23.39  thf(t44_xboole_1, axiom,
% 23.13/23.39    (![A:$i,B:$i,C:$i]:
% 23.13/23.39     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 23.13/23.39       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 23.13/23.39  thf('31', plain,
% 23.13/23.39      (![X14 : $i, X15 : $i, X16 : $i]:
% 23.13/23.39         ((r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 23.13/23.39          | ~ (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16))),
% 23.13/23.39      inference('cnf', [status(esa)], [t44_xboole_1])).
% 23.13/23.39  thf('32', plain,
% 23.13/23.39      (![X0 : $i, X1 : $i]:
% 23.13/23.39         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 23.13/23.39      inference('sup-', [status(thm)], ['30', '31'])).
% 23.13/23.39  thf('33', plain,
% 23.13/23.39      (![X0 : $i, X1 : $i]:
% 23.13/23.39         (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ (k3_subset_1 @ X0 @ X0)))),
% 23.13/23.39      inference('sup+', [status(thm)], ['29', '32'])).
% 23.13/23.39  thf('34', plain,
% 23.13/23.39      (![X0 : $i, X2 : $i]:
% 23.13/23.39         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 23.13/23.39      inference('cnf', [status(esa)], [d10_xboole_0])).
% 23.13/23.39  thf('35', plain,
% 23.13/23.39      (![X0 : $i, X1 : $i]:
% 23.13/23.39         (~ (r1_tarski @ (k4_xboole_0 @ X1 @ (k3_subset_1 @ X0 @ X0)) @ X1)
% 23.13/23.39          | ((k4_xboole_0 @ X1 @ (k3_subset_1 @ X0 @ X0)) = (X1)))),
% 23.13/23.39      inference('sup-', [status(thm)], ['33', '34'])).
% 23.13/23.39  thf('36', plain,
% 23.13/23.39      (![X0 : $i, X1 : $i]:
% 23.13/23.39         ((k2_xboole_0 @ (k3_subset_1 @ X1 @ X1) @ X0) = (X0))),
% 23.13/23.39      inference('demod', [status(thm)], ['13', '23'])).
% 23.13/23.39  thf('37', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 23.13/23.39      inference('simplify', [status(thm)], ['7'])).
% 23.13/23.39  thf('38', plain,
% 23.13/23.39      (![X11 : $i, X12 : $i, X13 : $i]:
% 23.13/23.39         ((r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 23.13/23.39          | ~ (r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 23.13/23.39      inference('cnf', [status(esa)], [t43_xboole_1])).
% 23.13/23.39  thf('39', plain,
% 23.13/23.39      (![X0 : $i, X1 : $i]:
% 23.13/23.39         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 23.13/23.39      inference('sup-', [status(thm)], ['37', '38'])).
% 23.13/23.39  thf('40', plain,
% 23.13/23.39      (![X0 : $i, X1 : $i]:
% 23.13/23.39         (r1_tarski @ (k4_xboole_0 @ X0 @ (k3_subset_1 @ X1 @ X1)) @ X0)),
% 23.13/23.39      inference('sup+', [status(thm)], ['36', '39'])).
% 23.13/23.39  thf('41', plain,
% 23.13/23.39      (![X0 : $i, X1 : $i]:
% 23.13/23.39         ((k4_xboole_0 @ X1 @ (k3_subset_1 @ X0 @ X0)) = (X1))),
% 23.13/23.39      inference('demod', [status(thm)], ['35', '40'])).
% 23.13/23.39  thf('42', plain,
% 23.13/23.39      (![X0 : $i, X2 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X2)),
% 23.13/23.39      inference('demod', [status(thm)], ['28', '41'])).
% 23.13/23.39  thf('43', plain,
% 23.13/23.39      (![X14 : $i, X15 : $i, X16 : $i]:
% 23.13/23.39         ((r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 23.13/23.39          | ~ (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16))),
% 23.13/23.39      inference('cnf', [status(esa)], [t44_xboole_1])).
% 23.13/23.39  thf('44', plain,
% 23.13/23.39      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 23.13/23.39      inference('sup-', [status(thm)], ['42', '43'])).
% 23.13/23.39  thf('45', plain,
% 23.13/23.39      (![X3 : $i, X4 : $i]:
% 23.13/23.39         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 23.13/23.39      inference('cnf', [status(esa)], [t12_xboole_1])).
% 23.13/23.39  thf('46', plain,
% 23.13/23.39      (![X0 : $i, X1 : $i]:
% 23.13/23.39         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 23.13/23.39           = (k2_xboole_0 @ X1 @ X0))),
% 23.13/23.39      inference('sup-', [status(thm)], ['44', '45'])).
% 23.13/23.39  thf('47', plain,
% 23.13/23.39      (![X0 : $i, X1 : $i]:
% 23.13/23.39         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 23.13/23.39      inference('sup-', [status(thm)], ['37', '38'])).
% 23.13/23.39  thf('48', plain,
% 23.13/23.39      (![X3 : $i, X4 : $i]:
% 23.13/23.39         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 23.13/23.39      inference('cnf', [status(esa)], [t12_xboole_1])).
% 23.13/23.39  thf('49', plain,
% 23.13/23.39      (![X0 : $i, X1 : $i]:
% 23.13/23.39         ((k2_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 23.13/23.39           = (X0))),
% 23.13/23.39      inference('sup-', [status(thm)], ['47', '48'])).
% 23.13/23.39  thf('50', plain,
% 23.13/23.39      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 23.13/23.39      inference('cnf', [status(esa)], [t7_xboole_1])).
% 23.13/23.39  thf('51', plain,
% 23.13/23.39      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 23.13/23.39      inference('cnf', [status(esa)], [t7_xboole_1])).
% 23.13/23.39  thf(t1_xboole_1, axiom,
% 23.13/23.39    (![A:$i,B:$i,C:$i]:
% 23.13/23.39     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 23.13/23.39       ( r1_tarski @ A @ C ) ))).
% 23.13/23.39  thf('52', plain,
% 23.13/23.39      (![X5 : $i, X6 : $i, X7 : $i]:
% 23.13/23.39         (~ (r1_tarski @ X5 @ X6)
% 23.13/23.39          | ~ (r1_tarski @ X6 @ X7)
% 23.13/23.40          | (r1_tarski @ X5 @ X7))),
% 23.13/23.40      inference('cnf', [status(esa)], [t1_xboole_1])).
% 23.13/23.40  thf('53', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.13/23.40         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 23.13/23.40      inference('sup-', [status(thm)], ['51', '52'])).
% 23.13/23.40  thf('54', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.13/23.40         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 23.13/23.40      inference('sup-', [status(thm)], ['50', '53'])).
% 23.13/23.40  thf('55', plain,
% 23.13/23.40      (![X14 : $i, X15 : $i, X16 : $i]:
% 23.13/23.40         ((r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 23.13/23.40          | ~ (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16))),
% 23.13/23.40      inference('cnf', [status(esa)], [t44_xboole_1])).
% 23.13/23.40  thf('56', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 23.13/23.40         (r1_tarski @ X3 @ 
% 23.13/23.40          (k2_xboole_0 @ X2 @ 
% 23.13/23.40           (k2_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X3 @ X2) @ X1) @ X0)))),
% 23.13/23.40      inference('sup-', [status(thm)], ['54', '55'])).
% 23.13/23.40  thf('57', plain,
% 23.13/23.40      (![X5 : $i, X6 : $i, X7 : $i]:
% 23.13/23.40         (~ (r1_tarski @ X5 @ X6)
% 23.13/23.40          | ~ (r1_tarski @ X6 @ X7)
% 23.13/23.40          | (r1_tarski @ X5 @ X7))),
% 23.13/23.40      inference('cnf', [status(esa)], [t1_xboole_1])).
% 23.13/23.40  thf('58', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 23.13/23.40         ((r1_tarski @ X3 @ X4)
% 23.13/23.40          | ~ (r1_tarski @ 
% 23.13/23.40               (k2_xboole_0 @ X2 @ 
% 23.13/23.40                (k2_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X3 @ X2) @ X1) @ 
% 23.13/23.40                 X0)) @ 
% 23.13/23.40               X4))),
% 23.13/23.40      inference('sup-', [status(thm)], ['56', '57'])).
% 23.13/23.40  thf('59', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 23.13/23.40         (~ (r1_tarski @ (k2_xboole_0 @ X3 @ (k2_xboole_0 @ X0 @ X2)) @ X1)
% 23.13/23.40          | (r1_tarski @ (k2_xboole_0 @ X3 @ X0) @ X1))),
% 23.13/23.40      inference('sup-', [status(thm)], ['49', '58'])).
% 23.13/23.40  thf('60', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.13/23.40         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 23.13/23.40          | (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X2))),
% 23.13/23.40      inference('sup-', [status(thm)], ['46', '59'])).
% 23.13/23.40  thf('61', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i]:
% 23.13/23.40         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 23.13/23.40      inference('sup-', [status(thm)], ['8', '60'])).
% 23.13/23.40  thf('62', plain,
% 23.13/23.40      (![X0 : $i, X2 : $i]:
% 23.13/23.40         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 23.13/23.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 23.13/23.40  thf('63', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i]:
% 23.13/23.40         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 23.13/23.40          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1)))),
% 23.13/23.40      inference('sup-', [status(thm)], ['61', '62'])).
% 23.13/23.40  thf('64', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i]:
% 23.13/23.40         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 23.13/23.40      inference('sup-', [status(thm)], ['8', '60'])).
% 23.13/23.40  thf('65', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 23.13/23.40      inference('demod', [status(thm)], ['63', '64'])).
% 23.13/23.40  thf('66', plain,
% 23.13/23.40      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 23.13/23.40          (k3_subset_1 @ sk_A @ sk_B))),
% 23.13/23.40      inference('demod', [status(thm)], ['6', '65'])).
% 23.13/23.40  thf('67', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 23.13/23.40      inference('simplify', [status(thm)], ['7'])).
% 23.13/23.40  thf('68', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 23.13/23.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.13/23.40  thf('69', plain,
% 23.13/23.40      (![X24 : $i, X25 : $i]:
% 23.13/23.40         (~ (m1_subset_1 @ X24 @ X25)
% 23.13/23.40          | (r2_hidden @ X24 @ X25)
% 23.13/23.40          | (v1_xboole_0 @ X25))),
% 23.13/23.40      inference('cnf', [status(esa)], [d2_subset_1])).
% 23.13/23.40  thf('70', plain,
% 23.13/23.40      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 23.13/23.40        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 23.13/23.40      inference('sup-', [status(thm)], ['68', '69'])).
% 23.13/23.40  thf('71', plain, (![X29 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 23.13/23.40      inference('cnf', [status(esa)], [fc1_subset_1])).
% 23.13/23.40  thf('72', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 23.13/23.40      inference('clc', [status(thm)], ['70', '71'])).
% 23.13/23.40  thf('73', plain,
% 23.13/23.40      (![X20 : $i, X21 : $i, X22 : $i]:
% 23.13/23.40         (~ (r2_hidden @ X22 @ X21)
% 23.13/23.40          | (r1_tarski @ X22 @ X20)
% 23.13/23.40          | ((X21) != (k1_zfmisc_1 @ X20)))),
% 23.13/23.40      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 23.13/23.40  thf('74', plain,
% 23.13/23.40      (![X20 : $i, X22 : $i]:
% 23.13/23.40         ((r1_tarski @ X22 @ X20) | ~ (r2_hidden @ X22 @ (k1_zfmisc_1 @ X20)))),
% 23.13/23.40      inference('simplify', [status(thm)], ['73'])).
% 23.13/23.40  thf('75', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 23.13/23.40      inference('sup-', [status(thm)], ['72', '74'])).
% 23.13/23.40  thf('76', plain,
% 23.13/23.40      (![X3 : $i, X4 : $i]:
% 23.13/23.40         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 23.13/23.40      inference('cnf', [status(esa)], [t12_xboole_1])).
% 23.13/23.40  thf('77', plain, (((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 23.13/23.40      inference('sup-', [status(thm)], ['75', '76'])).
% 23.13/23.40  thf('78', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 23.13/23.40      inference('sup-', [status(thm)], ['42', '43'])).
% 23.13/23.40  thf('79', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 23.13/23.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.13/23.40  thf('80', plain,
% 23.13/23.40      (![X24 : $i, X25 : $i]:
% 23.13/23.40         (~ (m1_subset_1 @ X24 @ X25)
% 23.13/23.40          | (r2_hidden @ X24 @ X25)
% 23.13/23.40          | (v1_xboole_0 @ X25))),
% 23.13/23.40      inference('cnf', [status(esa)], [d2_subset_1])).
% 23.13/23.40  thf('81', plain,
% 23.13/23.40      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 23.13/23.40        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 23.13/23.40      inference('sup-', [status(thm)], ['79', '80'])).
% 23.13/23.40  thf('82', plain, (![X29 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 23.13/23.40      inference('cnf', [status(esa)], [fc1_subset_1])).
% 23.13/23.40  thf('83', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 23.13/23.40      inference('clc', [status(thm)], ['81', '82'])).
% 23.13/23.40  thf('84', plain,
% 23.13/23.40      (![X20 : $i, X22 : $i]:
% 23.13/23.40         ((r1_tarski @ X22 @ X20) | ~ (r2_hidden @ X22 @ (k1_zfmisc_1 @ X20)))),
% 23.13/23.40      inference('simplify', [status(thm)], ['73'])).
% 23.13/23.40  thf('85', plain, ((r1_tarski @ sk_B @ sk_A)),
% 23.13/23.40      inference('sup-', [status(thm)], ['83', '84'])).
% 23.13/23.40  thf('86', plain,
% 23.13/23.40      (![X5 : $i, X6 : $i, X7 : $i]:
% 23.13/23.40         (~ (r1_tarski @ X5 @ X6)
% 23.13/23.40          | ~ (r1_tarski @ X6 @ X7)
% 23.13/23.40          | (r1_tarski @ X5 @ X7))),
% 23.13/23.40      inference('cnf', [status(esa)], [t1_xboole_1])).
% 23.13/23.40  thf('87', plain,
% 23.13/23.40      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 23.13/23.40      inference('sup-', [status(thm)], ['85', '86'])).
% 23.13/23.40  thf('88', plain,
% 23.13/23.40      (![X0 : $i]: (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ sk_A))),
% 23.13/23.40      inference('sup-', [status(thm)], ['78', '87'])).
% 23.13/23.40  thf('89', plain,
% 23.13/23.40      (![X3 : $i, X4 : $i]:
% 23.13/23.40         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 23.13/23.40      inference('cnf', [status(esa)], [t12_xboole_1])).
% 23.13/23.40  thf('90', plain,
% 23.13/23.40      (![X0 : $i]:
% 23.13/23.40         ((k2_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_A))
% 23.13/23.40           = (k2_xboole_0 @ X0 @ sk_A))),
% 23.13/23.40      inference('sup-', [status(thm)], ['88', '89'])).
% 23.13/23.40  thf('91', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 23.13/23.40         (~ (r1_tarski @ (k2_xboole_0 @ X3 @ (k2_xboole_0 @ X0 @ X2)) @ X1)
% 23.13/23.40          | (r1_tarski @ (k2_xboole_0 @ X3 @ X0) @ X1))),
% 23.13/23.40      inference('sup-', [status(thm)], ['49', '58'])).
% 23.13/23.40  thf('92', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i]:
% 23.13/23.40         (~ (r1_tarski @ (k2_xboole_0 @ X0 @ sk_A) @ X1)
% 23.13/23.40          | (r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ X1))),
% 23.13/23.40      inference('sup-', [status(thm)], ['90', '91'])).
% 23.13/23.40  thf('93', plain,
% 23.13/23.40      (![X0 : $i]:
% 23.13/23.40         (~ (r1_tarski @ sk_A @ X0)
% 23.13/23.40          | (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C_1) @ X0))),
% 23.13/23.40      inference('sup-', [status(thm)], ['77', '92'])).
% 23.13/23.40  thf('94', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 23.13/23.40      inference('demod', [status(thm)], ['63', '64'])).
% 23.13/23.40  thf('95', plain,
% 23.13/23.40      (![X0 : $i]:
% 23.13/23.40         (~ (r1_tarski @ sk_A @ X0)
% 23.13/23.40          | (r1_tarski @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ X0))),
% 23.13/23.40      inference('demod', [status(thm)], ['93', '94'])).
% 23.13/23.40  thf('96', plain, ((r1_tarski @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A)),
% 23.13/23.40      inference('sup-', [status(thm)], ['67', '95'])).
% 23.13/23.40  thf('97', plain,
% 23.13/23.40      (![X3 : $i, X4 : $i]:
% 23.13/23.40         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 23.13/23.40      inference('cnf', [status(esa)], [t12_xboole_1])).
% 23.13/23.40  thf('98', plain,
% 23.13/23.40      (((k2_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A) = (sk_A))),
% 23.13/23.40      inference('sup-', [status(thm)], ['96', '97'])).
% 23.13/23.40  thf('99', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 23.13/23.40      inference('demod', [status(thm)], ['63', '64'])).
% 23.13/23.40  thf('100', plain,
% 23.13/23.40      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) = (sk_A))),
% 23.13/23.40      inference('demod', [status(thm)], ['98', '99'])).
% 23.13/23.40  thf('101', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i]:
% 23.13/23.40         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 23.13/23.40           = (k2_xboole_0 @ X1 @ X0))),
% 23.13/23.40      inference('sup-', [status(thm)], ['44', '45'])).
% 23.13/23.40  thf('102', plain,
% 23.13/23.40      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 23.13/23.40      inference('cnf', [status(esa)], [t7_xboole_1])).
% 23.13/23.40  thf('103', plain,
% 23.13/23.40      (![X19 : $i, X20 : $i]:
% 23.13/23.40         ((r2_hidden @ X19 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X19 @ X20))),
% 23.13/23.40      inference('simplify', [status(thm)], ['15'])).
% 23.13/23.40  thf('104', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i]:
% 23.13/23.40         (r2_hidden @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 23.13/23.40      inference('sup-', [status(thm)], ['102', '103'])).
% 23.13/23.40  thf('105', plain,
% 23.13/23.40      (![X24 : $i, X25 : $i]:
% 23.13/23.40         (~ (r2_hidden @ X24 @ X25)
% 23.13/23.40          | (m1_subset_1 @ X24 @ X25)
% 23.13/23.40          | (v1_xboole_0 @ X25))),
% 23.13/23.40      inference('cnf', [status(esa)], [d2_subset_1])).
% 23.13/23.40  thf('106', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i]:
% 23.13/23.40         ((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 23.13/23.40          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 23.13/23.40      inference('sup-', [status(thm)], ['104', '105'])).
% 23.13/23.40  thf('107', plain, (![X29 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 23.13/23.40      inference('cnf', [status(esa)], [fc1_subset_1])).
% 23.13/23.40  thf('108', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i]:
% 23.13/23.40         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 23.13/23.40      inference('clc', [status(thm)], ['106', '107'])).
% 23.13/23.40  thf('109', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i]:
% 23.13/23.40         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 23.13/23.40      inference('sup+', [status(thm)], ['101', '108'])).
% 23.13/23.40  thf('110', plain,
% 23.13/23.40      (![X27 : $i, X28 : $i]:
% 23.13/23.40         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 23.13/23.40          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 23.13/23.40      inference('cnf', [status(esa)], [d5_subset_1])).
% 23.13/23.40  thf('111', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i]:
% 23.13/23.40         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 23.13/23.40           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 23.13/23.40      inference('sup-', [status(thm)], ['109', '110'])).
% 23.13/23.40  thf('112', plain,
% 23.13/23.40      (((k3_subset_1 @ (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 23.13/23.40         (k2_xboole_0 @ sk_C_1 @ sk_B))
% 23.13/23.40         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 23.13/23.40      inference('sup+', [status(thm)], ['100', '111'])).
% 23.13/23.40  thf('113', plain,
% 23.13/23.40      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) = (sk_A))),
% 23.13/23.40      inference('demod', [status(thm)], ['98', '99'])).
% 23.13/23.40  thf('114', plain,
% 23.13/23.40      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 23.13/23.40         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 23.13/23.40      inference('demod', [status(thm)], ['112', '113'])).
% 23.13/23.40  thf('115', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 23.13/23.40      inference('sup-', [status(thm)], ['42', '43'])).
% 23.13/23.40  thf('116', plain,
% 23.13/23.40      (![X8 : $i, X9 : $i, X10 : $i]:
% 23.13/23.40         (~ (r1_tarski @ X8 @ X9)
% 23.13/23.40          | (r1_tarski @ (k4_xboole_0 @ X10 @ X9) @ (k4_xboole_0 @ X10 @ X8)))),
% 23.13/23.40      inference('cnf', [status(esa)], [t34_xboole_1])).
% 23.13/23.40  thf('117', plain,
% 23.13/23.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.13/23.40         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 23.13/23.40          (k4_xboole_0 @ X2 @ X0))),
% 23.13/23.40      inference('sup-', [status(thm)], ['115', '116'])).
% 23.13/23.40  thf('118', plain,
% 23.13/23.40      ((r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 23.13/23.40        (k4_xboole_0 @ sk_A @ sk_B))),
% 23.13/23.40      inference('sup+', [status(thm)], ['114', '117'])).
% 23.13/23.40  thf('119', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 23.13/23.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.13/23.40  thf('120', plain,
% 23.13/23.40      (![X27 : $i, X28 : $i]:
% 23.13/23.40         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 23.13/23.40          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 23.13/23.40      inference('cnf', [status(esa)], [d5_subset_1])).
% 23.13/23.40  thf('121', plain,
% 23.13/23.40      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 23.13/23.40      inference('sup-', [status(thm)], ['119', '120'])).
% 23.13/23.40  thf('122', plain,
% 23.13/23.40      ((r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 23.13/23.40        (k3_subset_1 @ sk_A @ sk_B))),
% 23.13/23.40      inference('demod', [status(thm)], ['118', '121'])).
% 23.13/23.40  thf('123', plain, ($false), inference('demod', [status(thm)], ['66', '122'])).
% 23.13/23.40  
% 23.13/23.40  % SZS output end Refutation
% 23.13/23.40  
% 23.13/23.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
