%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DPrEKlGsh5

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:46 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 768 expanded)
%              Number of leaves         :   26 ( 251 expanded)
%              Depth                    :   28
%              Number of atoms          :  890 (5861 expanded)
%              Number of equality atoms :   80 ( 414 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('4',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X19 )
      | ( X19
       != ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( m1_subset_1 @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X24 )
      | ( m1_subset_1 @ X24 @ X23 )
      | ~ ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('16',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_subset_1 @ X0 @ X1 )
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ( ( k3_subset_1 @ X0 @ X1 )
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['4','18'])).

thf('20',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X27: $i,X28: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ X0 )
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('38',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X30 @ ( k3_subset_1 @ X30 @ X29 ) )
        = X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X24 )
      | ( m1_subset_1 @ X24 @ X23 )
      | ~ ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('43',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X30 @ ( k3_subset_1 @ X30 @ X29 ) )
        = X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ X0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k3_subset_1 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['24','25'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k3_subset_1 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X24 )
      | ( m1_subset_1 @ X24 @ X23 )
      | ~ ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('54',plain,(
    ! [X27: $i,X28: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['28','56'])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['24','25'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( ( k3_subset_1 @ X0 @ X0 )
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['3','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','65'])).

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

thf('67',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('70',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['67','72'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('74',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_xboole_0 @ X14 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('76',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('84',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('88',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_xboole_0 @ X14 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    r1_xboole_0 @ sk_B @ sk_B ),
    inference('sup+',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('94',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('96',plain,
    ( ( k3_xboole_0 @ sk_B @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( sk_B
      = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['81','96'])).

thf('98',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('100',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DPrEKlGsh5
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:18:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.81/2.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.81/2.04  % Solved by: fo/fo7.sh
% 1.81/2.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.81/2.04  % done 2629 iterations in 1.587s
% 1.81/2.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.81/2.04  % SZS output start Refutation
% 1.81/2.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.81/2.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.81/2.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.81/2.04  thf(sk_B_type, type, sk_B: $i).
% 1.81/2.04  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.81/2.04  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.81/2.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.81/2.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.81/2.04  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.81/2.04  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.81/2.04  thf(sk_A_type, type, sk_A: $i).
% 1.81/2.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.81/2.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.81/2.04  thf(t3_boole, axiom,
% 1.81/2.04    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.81/2.04  thf('0', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.81/2.04      inference('cnf', [status(esa)], [t3_boole])).
% 1.81/2.04  thf(t48_xboole_1, axiom,
% 1.81/2.04    (![A:$i,B:$i]:
% 1.81/2.04     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.81/2.04  thf('1', plain,
% 1.81/2.04      (![X7 : $i, X8 : $i]:
% 1.81/2.04         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 1.81/2.04           = (k3_xboole_0 @ X7 @ X8))),
% 1.81/2.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.81/2.04  thf('2', plain,
% 1.81/2.04      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.81/2.04      inference('sup+', [status(thm)], ['0', '1'])).
% 1.81/2.04  thf('3', plain,
% 1.81/2.04      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.81/2.04      inference('sup+', [status(thm)], ['0', '1'])).
% 1.81/2.04  thf('4', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.81/2.04      inference('cnf', [status(esa)], [t3_boole])).
% 1.81/2.04  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.81/2.04  thf('5', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 1.81/2.04      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.81/2.04  thf(d1_zfmisc_1, axiom,
% 1.81/2.04    (![A:$i,B:$i]:
% 1.81/2.04     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.81/2.04       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.81/2.04  thf('6', plain,
% 1.81/2.04      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.81/2.04         (~ (r1_tarski @ X17 @ X18)
% 1.81/2.04          | (r2_hidden @ X17 @ X19)
% 1.81/2.04          | ((X19) != (k1_zfmisc_1 @ X18)))),
% 1.81/2.04      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.81/2.04  thf('7', plain,
% 1.81/2.04      (![X17 : $i, X18 : $i]:
% 1.81/2.04         ((r2_hidden @ X17 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X17 @ X18))),
% 1.81/2.04      inference('simplify', [status(thm)], ['6'])).
% 1.81/2.04  thf('8', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.81/2.04      inference('sup-', [status(thm)], ['5', '7'])).
% 1.81/2.04  thf(d2_subset_1, axiom,
% 1.81/2.04    (![A:$i,B:$i]:
% 1.81/2.04     ( ( ( v1_xboole_0 @ A ) =>
% 1.81/2.04         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.81/2.04       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.81/2.04         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.81/2.04  thf('9', plain,
% 1.81/2.04      (![X22 : $i, X23 : $i]:
% 1.81/2.04         (~ (r2_hidden @ X22 @ X23)
% 1.81/2.04          | (m1_subset_1 @ X22 @ X23)
% 1.81/2.04          | (v1_xboole_0 @ X23))),
% 1.81/2.04      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.81/2.04  thf('10', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.81/2.04          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 1.81/2.04      inference('sup-', [status(thm)], ['8', '9'])).
% 1.81/2.04  thf(d5_subset_1, axiom,
% 1.81/2.04    (![A:$i,B:$i]:
% 1.81/2.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.81/2.04       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.81/2.04  thf('11', plain,
% 1.81/2.04      (![X25 : $i, X26 : $i]:
% 1.81/2.04         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 1.81/2.04          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 1.81/2.04      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.81/2.04  thf('12', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.81/2.04          | ((k3_subset_1 @ X0 @ k1_xboole_0)
% 1.81/2.04              = (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.81/2.04      inference('sup-', [status(thm)], ['10', '11'])).
% 1.81/2.04  thf('13', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.81/2.04      inference('cnf', [status(esa)], [t3_boole])).
% 1.81/2.04  thf('14', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.81/2.04          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0)))),
% 1.81/2.04      inference('demod', [status(thm)], ['12', '13'])).
% 1.81/2.04  thf('15', plain,
% 1.81/2.04      (![X23 : $i, X24 : $i]:
% 1.81/2.04         (~ (v1_xboole_0 @ X24)
% 1.81/2.04          | (m1_subset_1 @ X24 @ X23)
% 1.81/2.04          | ~ (v1_xboole_0 @ X23))),
% 1.81/2.04      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.81/2.04  thf('16', plain,
% 1.81/2.04      (![X25 : $i, X26 : $i]:
% 1.81/2.04         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 1.81/2.04          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 1.81/2.04      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.81/2.04  thf('17', plain,
% 1.81/2.04      (![X0 : $i, X1 : $i]:
% 1.81/2.04         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.81/2.04          | ~ (v1_xboole_0 @ X1)
% 1.81/2.04          | ((k3_subset_1 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1)))),
% 1.81/2.04      inference('sup-', [status(thm)], ['15', '16'])).
% 1.81/2.04  thf('18', plain,
% 1.81/2.04      (![X0 : $i, X1 : $i]:
% 1.81/2.04         (((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 1.81/2.04          | ((k3_subset_1 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))
% 1.81/2.04          | ~ (v1_xboole_0 @ X1))),
% 1.81/2.04      inference('sup-', [status(thm)], ['14', '17'])).
% 1.81/2.04  thf('19', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         (((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 1.81/2.04          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.81/2.04          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0)))),
% 1.81/2.04      inference('sup+', [status(thm)], ['4', '18'])).
% 1.81/2.04  thf('20', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 1.81/2.04      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.81/2.04  thf(t106_xboole_1, axiom,
% 1.81/2.04    (![A:$i,B:$i,C:$i]:
% 1.81/2.04     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.81/2.04       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 1.81/2.04  thf('21', plain,
% 1.81/2.04      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.81/2.04         ((r1_xboole_0 @ X2 @ X4)
% 1.81/2.04          | ~ (r1_tarski @ X2 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.81/2.04      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.81/2.04  thf('22', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.81/2.04      inference('sup-', [status(thm)], ['20', '21'])).
% 1.81/2.04  thf(t69_xboole_1, axiom,
% 1.81/2.04    (![A:$i,B:$i]:
% 1.81/2.04     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.81/2.04       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 1.81/2.04  thf('23', plain,
% 1.81/2.04      (![X9 : $i, X10 : $i]:
% 1.81/2.04         (~ (r1_xboole_0 @ X9 @ X10)
% 1.81/2.04          | ~ (r1_tarski @ X9 @ X10)
% 1.81/2.04          | (v1_xboole_0 @ X9))),
% 1.81/2.04      inference('cnf', [status(esa)], [t69_xboole_1])).
% 1.81/2.04  thf('24', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         ((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 1.81/2.04      inference('sup-', [status(thm)], ['22', '23'])).
% 1.81/2.04  thf('25', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 1.81/2.04      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.81/2.04  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.81/2.04      inference('demod', [status(thm)], ['24', '25'])).
% 1.81/2.04  thf('27', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         (((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 1.81/2.04          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0)))),
% 1.81/2.04      inference('demod', [status(thm)], ['19', '26'])).
% 1.81/2.04  thf('28', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.81/2.04      inference('simplify', [status(thm)], ['27'])).
% 1.81/2.04  thf('29', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.81/2.04          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 1.81/2.04      inference('sup-', [status(thm)], ['8', '9'])).
% 1.81/2.04  thf(dt_k3_subset_1, axiom,
% 1.81/2.04    (![A:$i,B:$i]:
% 1.81/2.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.81/2.04       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.81/2.04  thf('30', plain,
% 1.81/2.04      (![X27 : $i, X28 : $i]:
% 1.81/2.04         ((m1_subset_1 @ (k3_subset_1 @ X27 @ X28) @ (k1_zfmisc_1 @ X27))
% 1.81/2.04          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 1.81/2.04      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.81/2.04  thf('31', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.81/2.04          | (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ 
% 1.81/2.04             (k1_zfmisc_1 @ X0)))),
% 1.81/2.04      inference('sup-', [status(thm)], ['29', '30'])).
% 1.81/2.04  thf('32', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.81/2.04      inference('simplify', [status(thm)], ['27'])).
% 1.81/2.04  thf('33', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.81/2.04          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 1.81/2.04      inference('demod', [status(thm)], ['31', '32'])).
% 1.81/2.04  thf('34', plain,
% 1.81/2.04      (![X25 : $i, X26 : $i]:
% 1.81/2.04         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 1.81/2.04          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 1.81/2.04      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.81/2.04  thf('35', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.81/2.04          | ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0)))),
% 1.81/2.04      inference('sup-', [status(thm)], ['33', '34'])).
% 1.81/2.04  thf('36', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.81/2.04      inference('simplify', [status(thm)], ['27'])).
% 1.81/2.04  thf('37', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.81/2.04          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 1.81/2.04      inference('sup-', [status(thm)], ['8', '9'])).
% 1.81/2.04  thf(involutiveness_k3_subset_1, axiom,
% 1.81/2.04    (![A:$i,B:$i]:
% 1.81/2.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.81/2.04       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.81/2.04  thf('38', plain,
% 1.81/2.04      (![X29 : $i, X30 : $i]:
% 1.81/2.04         (((k3_subset_1 @ X30 @ (k3_subset_1 @ X30 @ X29)) = (X29))
% 1.81/2.04          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30)))),
% 1.81/2.04      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.81/2.04  thf('39', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.81/2.04          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 1.81/2.04              = (k1_xboole_0)))),
% 1.81/2.04      inference('sup-', [status(thm)], ['37', '38'])).
% 1.81/2.04  thf('40', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.81/2.04      inference('simplify', [status(thm)], ['27'])).
% 1.81/2.04  thf('41', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.81/2.04          | ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0)))),
% 1.81/2.04      inference('demod', [status(thm)], ['39', '40'])).
% 1.81/2.04  thf('42', plain,
% 1.81/2.04      (![X23 : $i, X24 : $i]:
% 1.81/2.04         (~ (v1_xboole_0 @ X24)
% 1.81/2.04          | (m1_subset_1 @ X24 @ X23)
% 1.81/2.04          | ~ (v1_xboole_0 @ X23))),
% 1.81/2.04      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.81/2.04  thf('43', plain,
% 1.81/2.04      (![X29 : $i, X30 : $i]:
% 1.81/2.04         (((k3_subset_1 @ X30 @ (k3_subset_1 @ X30 @ X29)) = (X29))
% 1.81/2.04          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30)))),
% 1.81/2.04      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.81/2.04  thf('44', plain,
% 1.81/2.04      (![X0 : $i, X1 : $i]:
% 1.81/2.04         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.81/2.04          | ~ (v1_xboole_0 @ X1)
% 1.81/2.04          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X1)) = (X1)))),
% 1.81/2.04      inference('sup-', [status(thm)], ['42', '43'])).
% 1.81/2.04  thf('45', plain,
% 1.81/2.04      (![X0 : $i, X1 : $i]:
% 1.81/2.04         (((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))
% 1.81/2.04          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X1)) = (X1))
% 1.81/2.04          | ~ (v1_xboole_0 @ X1))),
% 1.81/2.04      inference('sup-', [status(thm)], ['41', '44'])).
% 1.81/2.04  thf('46', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         (((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))
% 1.81/2.04          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.81/2.04          | ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0)))),
% 1.81/2.04      inference('sup+', [status(thm)], ['36', '45'])).
% 1.81/2.04  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.81/2.04      inference('demod', [status(thm)], ['24', '25'])).
% 1.81/2.04  thf('48', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         (((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))
% 1.81/2.04          | ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0)))),
% 1.81/2.04      inference('demod', [status(thm)], ['46', '47'])).
% 1.81/2.04  thf('49', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.81/2.04      inference('simplify', [status(thm)], ['48'])).
% 1.81/2.04  thf('50', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.81/2.04          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 1.81/2.04      inference('demod', [status(thm)], ['35', '49'])).
% 1.81/2.04  thf('51', plain,
% 1.81/2.04      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.81/2.04      inference('sup+', [status(thm)], ['0', '1'])).
% 1.81/2.04  thf('52', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 1.81/2.04          | (v1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 1.81/2.04      inference('sup+', [status(thm)], ['50', '51'])).
% 1.81/2.04  thf('53', plain,
% 1.81/2.04      (![X23 : $i, X24 : $i]:
% 1.81/2.04         (~ (v1_xboole_0 @ X24)
% 1.81/2.04          | (m1_subset_1 @ X24 @ X23)
% 1.81/2.04          | ~ (v1_xboole_0 @ X23))),
% 1.81/2.04      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.81/2.04  thf('54', plain,
% 1.81/2.04      (![X27 : $i, X28 : $i]:
% 1.81/2.04         ((m1_subset_1 @ (k3_subset_1 @ X27 @ X28) @ (k1_zfmisc_1 @ X27))
% 1.81/2.04          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 1.81/2.04      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.81/2.04  thf('55', plain,
% 1.81/2.04      (![X0 : $i, X1 : $i]:
% 1.81/2.04         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.81/2.04          | ~ (v1_xboole_0 @ X1)
% 1.81/2.04          | (m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 1.81/2.04      inference('sup-', [status(thm)], ['53', '54'])).
% 1.81/2.04  thf('56', plain,
% 1.81/2.04      (![X0 : $i, X1 : $i]:
% 1.81/2.04         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 1.81/2.04          | (m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 1.81/2.04          | ~ (v1_xboole_0 @ X1))),
% 1.81/2.04      inference('sup-', [status(thm)], ['52', '55'])).
% 1.81/2.04  thf('57', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))
% 1.81/2.04          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.81/2.04          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.81/2.04      inference('sup+', [status(thm)], ['28', '56'])).
% 1.81/2.04  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.81/2.04      inference('demod', [status(thm)], ['24', '25'])).
% 1.81/2.04  thf('59', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))
% 1.81/2.04          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.81/2.04      inference('demod', [status(thm)], ['57', '58'])).
% 1.81/2.04  thf('60', plain,
% 1.81/2.04      (![X25 : $i, X26 : $i]:
% 1.81/2.04         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 1.81/2.04          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 1.81/2.04      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.81/2.04  thf('61', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 1.81/2.04          | ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0)))),
% 1.81/2.04      inference('sup-', [status(thm)], ['59', '60'])).
% 1.81/2.04  thf('62', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.81/2.04      inference('simplify', [status(thm)], ['48'])).
% 1.81/2.04  thf('63', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 1.81/2.04          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0)))),
% 1.81/2.04      inference('demod', [status(thm)], ['61', '62'])).
% 1.81/2.04  thf('64', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 1.81/2.04          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.81/2.04      inference('sup+', [status(thm)], ['3', '63'])).
% 1.81/2.04  thf('65', plain,
% 1.81/2.04      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.81/2.04      inference('simplify', [status(thm)], ['64'])).
% 1.81/2.04  thf('66', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.81/2.04      inference('demod', [status(thm)], ['2', '65'])).
% 1.81/2.04  thf(t40_subset_1, conjecture,
% 1.81/2.04    (![A:$i,B:$i,C:$i]:
% 1.81/2.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.81/2.04       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 1.81/2.04         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.81/2.04  thf(zf_stmt_0, negated_conjecture,
% 1.81/2.04    (~( ![A:$i,B:$i,C:$i]:
% 1.81/2.04        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.81/2.04          ( ( ( r1_tarski @ B @ C ) & 
% 1.81/2.04              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 1.81/2.04            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 1.81/2.04    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 1.81/2.04  thf('67', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 1.81/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.04  thf('68', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.81/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.04  thf('69', plain,
% 1.81/2.04      (![X25 : $i, X26 : $i]:
% 1.81/2.04         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 1.81/2.04          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 1.81/2.04      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.81/2.04  thf('70', plain,
% 1.81/2.04      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 1.81/2.04      inference('sup-', [status(thm)], ['68', '69'])).
% 1.81/2.04  thf('71', plain,
% 1.81/2.04      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.81/2.04         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ X2 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.81/2.04      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.81/2.04  thf('72', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 1.81/2.04          | (r1_tarski @ X0 @ sk_A))),
% 1.81/2.04      inference('sup-', [status(thm)], ['70', '71'])).
% 1.81/2.04  thf('73', plain, ((r1_tarski @ sk_B @ sk_A)),
% 1.81/2.04      inference('sup-', [status(thm)], ['67', '72'])).
% 1.81/2.04  thf(t85_xboole_1, axiom,
% 1.81/2.04    (![A:$i,B:$i,C:$i]:
% 1.81/2.04     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 1.81/2.04  thf('74', plain,
% 1.81/2.04      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.81/2.04         (~ (r1_tarski @ X14 @ X15)
% 1.81/2.04          | (r1_xboole_0 @ X14 @ (k4_xboole_0 @ X16 @ X15)))),
% 1.81/2.04      inference('cnf', [status(esa)], [t85_xboole_1])).
% 1.81/2.04  thf('75', plain,
% 1.81/2.04      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A))),
% 1.81/2.04      inference('sup-', [status(thm)], ['73', '74'])).
% 1.81/2.04  thf(t83_xboole_1, axiom,
% 1.81/2.04    (![A:$i,B:$i]:
% 1.81/2.04     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.81/2.04  thf('76', plain,
% 1.81/2.04      (![X11 : $i, X12 : $i]:
% 1.81/2.04         (((k4_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 1.81/2.04      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.81/2.04  thf('77', plain,
% 1.81/2.04      (![X0 : $i]: ((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A)) = (sk_B))),
% 1.81/2.04      inference('sup-', [status(thm)], ['75', '76'])).
% 1.81/2.04  thf('78', plain,
% 1.81/2.04      (![X7 : $i, X8 : $i]:
% 1.81/2.04         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 1.81/2.04           = (k3_xboole_0 @ X7 @ X8))),
% 1.81/2.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.81/2.04  thf('79', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         ((k4_xboole_0 @ sk_B @ sk_B)
% 1.81/2.04           = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A)))),
% 1.81/2.04      inference('sup+', [status(thm)], ['77', '78'])).
% 1.81/2.04  thf('80', plain,
% 1.81/2.04      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.81/2.04      inference('sup+', [status(thm)], ['0', '1'])).
% 1.81/2.04  thf('81', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         ((k3_xboole_0 @ sk_B @ k1_xboole_0)
% 1.81/2.04           = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A)))),
% 1.81/2.04      inference('demod', [status(thm)], ['79', '80'])).
% 1.81/2.04  thf('82', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 1.81/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.04  thf('83', plain,
% 1.81/2.04      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 1.81/2.04      inference('sup-', [status(thm)], ['68', '69'])).
% 1.81/2.04  thf('84', plain,
% 1.81/2.04      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.81/2.04         ((r1_xboole_0 @ X2 @ X4)
% 1.81/2.04          | ~ (r1_tarski @ X2 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.81/2.04      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.81/2.04  thf('85', plain,
% 1.81/2.04      (![X0 : $i]:
% 1.81/2.04         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 1.81/2.04          | (r1_xboole_0 @ X0 @ sk_C_1))),
% 1.81/2.04      inference('sup-', [status(thm)], ['83', '84'])).
% 1.81/2.04  thf('86', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 1.81/2.04      inference('sup-', [status(thm)], ['82', '85'])).
% 1.81/2.04  thf('87', plain,
% 1.81/2.04      (![X11 : $i, X12 : $i]:
% 1.81/2.04         (((k4_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 1.81/2.04      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.81/2.04  thf('88', plain, (((k4_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 1.81/2.04      inference('sup-', [status(thm)], ['86', '87'])).
% 1.81/2.04  thf('89', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 1.81/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.04  thf('90', plain,
% 1.81/2.04      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.81/2.04         (~ (r1_tarski @ X14 @ X15)
% 1.81/2.04          | (r1_xboole_0 @ X14 @ (k4_xboole_0 @ X16 @ X15)))),
% 1.81/2.04      inference('cnf', [status(esa)], [t85_xboole_1])).
% 1.81/2.04  thf('91', plain,
% 1.81/2.04      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1))),
% 1.81/2.04      inference('sup-', [status(thm)], ['89', '90'])).
% 1.81/2.04  thf('92', plain, ((r1_xboole_0 @ sk_B @ sk_B)),
% 1.81/2.04      inference('sup+', [status(thm)], ['88', '91'])).
% 1.81/2.04  thf('93', plain,
% 1.81/2.04      (![X11 : $i, X12 : $i]:
% 1.81/2.04         (((k4_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 1.81/2.04      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.81/2.04  thf('94', plain, (((k4_xboole_0 @ sk_B @ sk_B) = (sk_B))),
% 1.81/2.04      inference('sup-', [status(thm)], ['92', '93'])).
% 1.81/2.04  thf('95', plain,
% 1.81/2.04      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.81/2.04      inference('sup+', [status(thm)], ['0', '1'])).
% 1.81/2.04  thf('96', plain, (((k3_xboole_0 @ sk_B @ k1_xboole_0) = (sk_B))),
% 1.81/2.04      inference('demod', [status(thm)], ['94', '95'])).
% 1.81/2.04  thf('97', plain,
% 1.81/2.04      (![X0 : $i]: ((sk_B) = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A)))),
% 1.81/2.04      inference('demod', [status(thm)], ['81', '96'])).
% 1.81/2.04  thf('98', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ k1_xboole_0))),
% 1.81/2.04      inference('sup+', [status(thm)], ['66', '97'])).
% 1.81/2.04  thf('99', plain,
% 1.81/2.04      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.81/2.04      inference('simplify', [status(thm)], ['64'])).
% 1.81/2.04  thf('100', plain, (((sk_B) = (k1_xboole_0))),
% 1.81/2.04      inference('demod', [status(thm)], ['98', '99'])).
% 1.81/2.04  thf('101', plain, (((sk_B) != (k1_xboole_0))),
% 1.81/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.04  thf('102', plain, ($false),
% 1.81/2.04      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 1.81/2.04  
% 1.81/2.04  % SZS output end Refutation
% 1.81/2.04  
% 1.81/2.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
