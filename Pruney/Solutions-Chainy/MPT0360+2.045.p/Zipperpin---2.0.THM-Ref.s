%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fq4qJLVhhN

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:47 EST 2020

% Result     : Theorem 8.10s
% Output     : Refutation 8.10s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 750 expanded)
%              Number of leaves         :   24 ( 224 expanded)
%              Depth                    :   23
%              Number of atoms          :  830 (7108 expanded)
%              Number of equality atoms :   61 ( 437 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X21 )
      | ( X21
       != ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ( m1_subset_1 @ X24 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
    | ( ( k3_subset_1 @ sk_C_1 @ sk_B )
      = ( k4_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_xboole_0 @ X26 )
      | ( m1_subset_1 @ X26 @ X25 )
      | ~ ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_subset_1 @ X0 @ X1 )
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ sk_C_1 @ sk_B )
        = ( k4_xboole_0 @ sk_C_1 @ sk_B ) )
      | ( ( k3_subset_1 @ sk_C_1 @ X0 )
        = ( k4_xboole_0 @ sk_C_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( ( k3_subset_1 @ sk_C_1 @ sk_B )
     != ( k3_subset_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_B )
    | ( ( k3_subset_1 @ sk_C_1 @ sk_B )
      = ( k4_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( k3_subset_1 @ sk_C_1 @ sk_B )
      = ( k4_xboole_0 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_xboole_0 @ X13 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_subset_1 @ sk_C_1 @ sk_B )
    = ( k4_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['13','24'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( k3_subset_1 @ sk_C_1 @ sk_B )
    = ( k4_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['13','24'])).

thf('31',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ sk_B )
    = ( k3_subset_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = sk_B ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_xboole_0 @ X13 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_xboole_0 @ sk_B @ sk_B ),
    inference('sup+',[status(thm)],['37','40'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('42',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X16 @ X18 )
      | ( r1_tarski @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ sk_B ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('46',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k3_subset_1 @ sk_C_1 @ sk_B )
    = ( k4_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['13','24'])).

thf('48',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ( m1_subset_1 @ X24 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) ) )
    | ( ( k3_subset_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ sk_B )
      = ( k4_xboole_0 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ sk_B )
    = ( k3_subset_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) ) )
    | ( ( k3_subset_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ sk_B )
      = ( k3_subset_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_subset_1 @ X0 @ X1 )
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ sk_B )
        = ( k3_subset_1 @ sk_C_1 @ sk_B ) )
      | ( ( k3_subset_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ X0 )
        = ( k4_xboole_0 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k3_subset_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ sk_B )
      = ( k3_subset_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_B )
    | ( ( k3_subset_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ sk_B )
      = ( k3_subset_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['31','56'])).

thf('58',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['22','23'])).

thf('59',plain,
    ( ( ( k3_subset_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ sk_B )
      = ( k3_subset_1 @ sk_C_1 @ sk_B ) )
    | ( ( k3_subset_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ sk_B )
      = ( k3_subset_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k3_subset_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ sk_B )
    = ( k3_subset_1 @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('62',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X30 @ ( k3_subset_1 @ X30 @ X29 ) )
        = X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) ) )
    | ( ( k3_subset_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ ( k3_subset_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k3_subset_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ sk_B )
    = ( k3_subset_1 @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['59'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('65',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('66',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X30 @ ( k3_subset_1 @ X30 @ X29 ) )
        = X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('69',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('71',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) ) )
    | ( k1_xboole_0 = sk_B ) ),
    inference(demod,[status(thm)],['63','64','73'])).

thf('75',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_xboole_0 @ ( k1_zfmisc_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_xboole_0 @ X26 )
      | ( m1_subset_1 @ X26 @ X25 )
      | ~ ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('78',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X30 @ ( k3_subset_1 @ X30 @ X29 ) )
        = X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ ( k3_subset_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ X0 ) )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,
    ( ( ( k3_subset_1 @ ( k3_subset_1 @ sk_C_1 @ sk_B ) @ ( k3_subset_1 @ sk_C_1 @ sk_B ) )
      = sk_B )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['60','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('83',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['22','23'])).

thf('84',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fq4qJLVhhN
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:29:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 8.10/8.27  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.10/8.27  % Solved by: fo/fo7.sh
% 8.10/8.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.10/8.27  % done 13929 iterations in 7.804s
% 8.10/8.27  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.10/8.27  % SZS output start Refutation
% 8.10/8.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.10/8.27  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.10/8.27  thf(sk_A_type, type, sk_A: $i).
% 8.10/8.27  thf(sk_C_1_type, type, sk_C_1: $i).
% 8.10/8.27  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.10/8.27  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 8.10/8.27  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.10/8.27  thf(sk_B_type, type, sk_B: $i).
% 8.10/8.27  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 8.10/8.27  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.10/8.27  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 8.10/8.27  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.10/8.27  thf(t40_subset_1, conjecture,
% 8.10/8.27    (![A:$i,B:$i,C:$i]:
% 8.10/8.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 8.10/8.27       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 8.10/8.27         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 8.10/8.27  thf(zf_stmt_0, negated_conjecture,
% 8.10/8.27    (~( ![A:$i,B:$i,C:$i]:
% 8.10/8.27        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 8.10/8.27          ( ( ( r1_tarski @ B @ C ) & 
% 8.10/8.27              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 8.10/8.27            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 8.10/8.27    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 8.10/8.27  thf('0', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 8.10/8.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.27  thf(d1_zfmisc_1, axiom,
% 8.10/8.27    (![A:$i,B:$i]:
% 8.10/8.27     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 8.10/8.27       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 8.10/8.27  thf('1', plain,
% 8.10/8.27      (![X19 : $i, X20 : $i, X21 : $i]:
% 8.10/8.27         (~ (r1_tarski @ X19 @ X20)
% 8.10/8.27          | (r2_hidden @ X19 @ X21)
% 8.10/8.27          | ((X21) != (k1_zfmisc_1 @ X20)))),
% 8.10/8.27      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 8.10/8.27  thf('2', plain,
% 8.10/8.27      (![X19 : $i, X20 : $i]:
% 8.10/8.27         ((r2_hidden @ X19 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X19 @ X20))),
% 8.10/8.27      inference('simplify', [status(thm)], ['1'])).
% 8.10/8.27  thf('3', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_C_1))),
% 8.10/8.27      inference('sup-', [status(thm)], ['0', '2'])).
% 8.10/8.27  thf(d2_subset_1, axiom,
% 8.10/8.27    (![A:$i,B:$i]:
% 8.10/8.27     ( ( ( v1_xboole_0 @ A ) =>
% 8.10/8.27         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 8.10/8.27       ( ( ~( v1_xboole_0 @ A ) ) =>
% 8.10/8.27         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 8.10/8.27  thf('4', plain,
% 8.10/8.27      (![X24 : $i, X25 : $i]:
% 8.10/8.27         (~ (r2_hidden @ X24 @ X25)
% 8.10/8.27          | (m1_subset_1 @ X24 @ X25)
% 8.10/8.27          | (v1_xboole_0 @ X25))),
% 8.10/8.27      inference('cnf', [status(esa)], [d2_subset_1])).
% 8.10/8.27  thf('5', plain,
% 8.10/8.27      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_1))
% 8.10/8.27        | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_C_1)))),
% 8.10/8.27      inference('sup-', [status(thm)], ['3', '4'])).
% 8.10/8.27  thf(d5_subset_1, axiom,
% 8.10/8.27    (![A:$i,B:$i]:
% 8.10/8.27     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.10/8.27       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 8.10/8.27  thf('6', plain,
% 8.10/8.27      (![X27 : $i, X28 : $i]:
% 8.10/8.27         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 8.10/8.27          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 8.10/8.27      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.10/8.27  thf('7', plain,
% 8.10/8.27      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_1))
% 8.10/8.27        | ((k3_subset_1 @ sk_C_1 @ sk_B) = (k4_xboole_0 @ sk_C_1 @ sk_B)))),
% 8.10/8.27      inference('sup-', [status(thm)], ['5', '6'])).
% 8.10/8.27  thf('8', plain,
% 8.10/8.27      (![X25 : $i, X26 : $i]:
% 8.10/8.27         (~ (v1_xboole_0 @ X26)
% 8.10/8.27          | (m1_subset_1 @ X26 @ X25)
% 8.10/8.27          | ~ (v1_xboole_0 @ X25))),
% 8.10/8.27      inference('cnf', [status(esa)], [d2_subset_1])).
% 8.10/8.27  thf('9', plain,
% 8.10/8.27      (![X27 : $i, X28 : $i]:
% 8.10/8.27         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 8.10/8.27          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 8.10/8.27      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.10/8.27  thf('10', plain,
% 8.10/8.27      (![X0 : $i, X1 : $i]:
% 8.10/8.27         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 8.10/8.27          | ~ (v1_xboole_0 @ X1)
% 8.10/8.27          | ((k3_subset_1 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1)))),
% 8.10/8.27      inference('sup-', [status(thm)], ['8', '9'])).
% 8.10/8.27  thf('11', plain,
% 8.10/8.27      (![X0 : $i]:
% 8.10/8.27         (((k3_subset_1 @ sk_C_1 @ sk_B) = (k4_xboole_0 @ sk_C_1 @ sk_B))
% 8.10/8.27          | ((k3_subset_1 @ sk_C_1 @ X0) = (k4_xboole_0 @ sk_C_1 @ X0))
% 8.10/8.27          | ~ (v1_xboole_0 @ X0))),
% 8.10/8.27      inference('sup-', [status(thm)], ['7', '10'])).
% 8.10/8.27  thf('12', plain,
% 8.10/8.27      ((((k3_subset_1 @ sk_C_1 @ sk_B) != (k3_subset_1 @ sk_C_1 @ sk_B))
% 8.10/8.27        | ~ (v1_xboole_0 @ sk_B)
% 8.10/8.27        | ((k3_subset_1 @ sk_C_1 @ sk_B) = (k4_xboole_0 @ sk_C_1 @ sk_B)))),
% 8.10/8.27      inference('eq_fact', [status(thm)], ['11'])).
% 8.10/8.27  thf('13', plain,
% 8.10/8.27      ((((k3_subset_1 @ sk_C_1 @ sk_B) = (k4_xboole_0 @ sk_C_1 @ sk_B))
% 8.10/8.27        | ~ (v1_xboole_0 @ sk_B))),
% 8.10/8.27      inference('simplify', [status(thm)], ['12'])).
% 8.10/8.27  thf('14', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 8.10/8.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.27  thf('15', plain,
% 8.10/8.27      (![X27 : $i, X28 : $i]:
% 8.10/8.27         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 8.10/8.27          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 8.10/8.27      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.10/8.27  thf('16', plain,
% 8.10/8.27      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 8.10/8.27      inference('sup-', [status(thm)], ['14', '15'])).
% 8.10/8.27  thf('17', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 8.10/8.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.27  thf(t85_xboole_1, axiom,
% 8.10/8.27    (![A:$i,B:$i,C:$i]:
% 8.10/8.27     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 8.10/8.27  thf('18', plain,
% 8.10/8.27      (![X13 : $i, X14 : $i, X15 : $i]:
% 8.10/8.27         (~ (r1_tarski @ X13 @ X14)
% 8.10/8.27          | (r1_xboole_0 @ X13 @ (k4_xboole_0 @ X15 @ X14)))),
% 8.10/8.27      inference('cnf', [status(esa)], [t85_xboole_1])).
% 8.10/8.27  thf('19', plain,
% 8.10/8.27      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1))),
% 8.10/8.27      inference('sup-', [status(thm)], ['17', '18'])).
% 8.10/8.27  thf(t69_xboole_1, axiom,
% 8.10/8.27    (![A:$i,B:$i]:
% 8.10/8.27     ( ( ~( v1_xboole_0 @ B ) ) =>
% 8.10/8.27       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 8.10/8.27  thf('20', plain,
% 8.10/8.27      (![X6 : $i, X7 : $i]:
% 8.10/8.27         (~ (r1_xboole_0 @ X6 @ X7)
% 8.10/8.27          | ~ (r1_tarski @ X6 @ X7)
% 8.10/8.27          | (v1_xboole_0 @ X6))),
% 8.10/8.27      inference('cnf', [status(esa)], [t69_xboole_1])).
% 8.10/8.27  thf('21', plain,
% 8.10/8.27      (![X0 : $i]:
% 8.10/8.27         ((v1_xboole_0 @ sk_B)
% 8.10/8.27          | ~ (r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1)))),
% 8.10/8.27      inference('sup-', [status(thm)], ['19', '20'])).
% 8.10/8.27  thf('22', plain,
% 8.10/8.27      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))
% 8.10/8.27        | (v1_xboole_0 @ sk_B))),
% 8.10/8.27      inference('sup-', [status(thm)], ['16', '21'])).
% 8.10/8.27  thf('23', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 8.10/8.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.27  thf('24', plain, ((v1_xboole_0 @ sk_B)),
% 8.10/8.27      inference('demod', [status(thm)], ['22', '23'])).
% 8.10/8.27  thf('25', plain,
% 8.10/8.27      (((k3_subset_1 @ sk_C_1 @ sk_B) = (k4_xboole_0 @ sk_C_1 @ sk_B))),
% 8.10/8.27      inference('demod', [status(thm)], ['13', '24'])).
% 8.10/8.27  thf(t79_xboole_1, axiom,
% 8.10/8.27    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 8.10/8.27  thf('26', plain,
% 8.10/8.27      (![X8 : $i, X9 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X9)),
% 8.10/8.27      inference('cnf', [status(esa)], [t79_xboole_1])).
% 8.10/8.27  thf(t83_xboole_1, axiom,
% 8.10/8.27    (![A:$i,B:$i]:
% 8.10/8.27     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 8.10/8.27  thf('27', plain,
% 8.10/8.27      (![X10 : $i, X11 : $i]:
% 8.10/8.27         (((k4_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_xboole_0 @ X10 @ X11))),
% 8.10/8.27      inference('cnf', [status(esa)], [t83_xboole_1])).
% 8.10/8.27  thf('28', plain,
% 8.10/8.27      (![X0 : $i, X1 : $i]:
% 8.10/8.27         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 8.10/8.27           = (k4_xboole_0 @ X1 @ X0))),
% 8.10/8.27      inference('sup-', [status(thm)], ['26', '27'])).
% 8.10/8.27  thf('29', plain,
% 8.10/8.27      (((k4_xboole_0 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ sk_B)
% 8.10/8.27         = (k4_xboole_0 @ sk_C_1 @ sk_B))),
% 8.10/8.27      inference('sup+', [status(thm)], ['25', '28'])).
% 8.10/8.27  thf('30', plain,
% 8.10/8.27      (((k3_subset_1 @ sk_C_1 @ sk_B) = (k4_xboole_0 @ sk_C_1 @ sk_B))),
% 8.10/8.27      inference('demod', [status(thm)], ['13', '24'])).
% 8.10/8.27  thf('31', plain,
% 8.10/8.27      (((k4_xboole_0 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ sk_B)
% 8.10/8.27         = (k3_subset_1 @ sk_C_1 @ sk_B))),
% 8.10/8.27      inference('demod', [status(thm)], ['29', '30'])).
% 8.10/8.27  thf('32', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 8.10/8.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.27  thf('33', plain,
% 8.10/8.27      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 8.10/8.27      inference('sup-', [status(thm)], ['14', '15'])).
% 8.10/8.27  thf('34', plain,
% 8.10/8.27      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1))),
% 8.10/8.27      inference('sup-', [status(thm)], ['17', '18'])).
% 8.10/8.27  thf('35', plain,
% 8.10/8.27      (![X10 : $i, X11 : $i]:
% 8.10/8.27         (((k4_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_xboole_0 @ X10 @ X11))),
% 8.10/8.27      inference('cnf', [status(esa)], [t83_xboole_1])).
% 8.10/8.27  thf('36', plain,
% 8.10/8.27      (![X0 : $i]:
% 8.10/8.27         ((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1)) = (sk_B))),
% 8.10/8.27      inference('sup-', [status(thm)], ['34', '35'])).
% 8.10/8.27  thf('37', plain,
% 8.10/8.27      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)) = (sk_B))),
% 8.10/8.27      inference('sup+', [status(thm)], ['33', '36'])).
% 8.10/8.27  thf('38', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 8.10/8.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.27  thf('39', plain,
% 8.10/8.27      (![X13 : $i, X14 : $i, X15 : $i]:
% 8.10/8.27         (~ (r1_tarski @ X13 @ X14)
% 8.10/8.27          | (r1_xboole_0 @ X13 @ (k4_xboole_0 @ X15 @ X14)))),
% 8.10/8.27      inference('cnf', [status(esa)], [t85_xboole_1])).
% 8.10/8.27  thf('40', plain,
% 8.10/8.27      (![X0 : $i]:
% 8.10/8.27         (r1_xboole_0 @ sk_B @ 
% 8.10/8.27          (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 8.10/8.27      inference('sup-', [status(thm)], ['38', '39'])).
% 8.10/8.27  thf('41', plain, ((r1_xboole_0 @ sk_B @ sk_B)),
% 8.10/8.27      inference('sup+', [status(thm)], ['37', '40'])).
% 8.10/8.27  thf(t86_xboole_1, axiom,
% 8.10/8.27    (![A:$i,B:$i,C:$i]:
% 8.10/8.27     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 8.10/8.27       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 8.10/8.27  thf('42', plain,
% 8.10/8.27      (![X16 : $i, X17 : $i, X18 : $i]:
% 8.10/8.27         (~ (r1_tarski @ X16 @ X17)
% 8.10/8.27          | ~ (r1_xboole_0 @ X16 @ X18)
% 8.10/8.27          | (r1_tarski @ X16 @ (k4_xboole_0 @ X17 @ X18)))),
% 8.10/8.27      inference('cnf', [status(esa)], [t86_xboole_1])).
% 8.10/8.27  thf('43', plain,
% 8.10/8.27      (![X0 : $i]:
% 8.10/8.27         ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_B))
% 8.10/8.27          | ~ (r1_tarski @ sk_B @ X0))),
% 8.10/8.27      inference('sup-', [status(thm)], ['41', '42'])).
% 8.10/8.27  thf('44', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_C_1 @ sk_B))),
% 8.10/8.27      inference('sup-', [status(thm)], ['32', '43'])).
% 8.10/8.27  thf('45', plain,
% 8.10/8.27      (![X19 : $i, X20 : $i]:
% 8.10/8.27         ((r2_hidden @ X19 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X19 @ X20))),
% 8.10/8.27      inference('simplify', [status(thm)], ['1'])).
% 8.10/8.27  thf('46', plain,
% 8.10/8.27      ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ (k4_xboole_0 @ sk_C_1 @ sk_B)))),
% 8.10/8.27      inference('sup-', [status(thm)], ['44', '45'])).
% 8.10/8.27  thf('47', plain,
% 8.10/8.27      (((k3_subset_1 @ sk_C_1 @ sk_B) = (k4_xboole_0 @ sk_C_1 @ sk_B))),
% 8.10/8.27      inference('demod', [status(thm)], ['13', '24'])).
% 8.10/8.27  thf('48', plain,
% 8.10/8.27      ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_C_1 @ sk_B)))),
% 8.10/8.27      inference('demod', [status(thm)], ['46', '47'])).
% 8.10/8.27  thf('49', plain,
% 8.10/8.27      (![X24 : $i, X25 : $i]:
% 8.10/8.27         (~ (r2_hidden @ X24 @ X25)
% 8.10/8.27          | (m1_subset_1 @ X24 @ X25)
% 8.10/8.27          | (v1_xboole_0 @ X25))),
% 8.10/8.27      inference('cnf', [status(esa)], [d2_subset_1])).
% 8.10/8.27  thf('50', plain,
% 8.10/8.27      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_C_1 @ sk_B)))
% 8.10/8.27        | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_C_1 @ sk_B))))),
% 8.10/8.27      inference('sup-', [status(thm)], ['48', '49'])).
% 8.10/8.27  thf('51', plain,
% 8.10/8.27      (![X27 : $i, X28 : $i]:
% 8.10/8.27         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 8.10/8.27          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 8.10/8.27      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.10/8.27  thf('52', plain,
% 8.10/8.27      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_C_1 @ sk_B)))
% 8.10/8.27        | ((k3_subset_1 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ sk_B)
% 8.10/8.27            = (k4_xboole_0 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ sk_B)))),
% 8.10/8.27      inference('sup-', [status(thm)], ['50', '51'])).
% 8.10/8.27  thf('53', plain,
% 8.10/8.27      (((k4_xboole_0 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ sk_B)
% 8.10/8.27         = (k3_subset_1 @ sk_C_1 @ sk_B))),
% 8.10/8.27      inference('demod', [status(thm)], ['29', '30'])).
% 8.10/8.27  thf('54', plain,
% 8.10/8.27      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_C_1 @ sk_B)))
% 8.10/8.27        | ((k3_subset_1 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ sk_B)
% 8.10/8.27            = (k3_subset_1 @ sk_C_1 @ sk_B)))),
% 8.10/8.27      inference('demod', [status(thm)], ['52', '53'])).
% 8.10/8.27  thf('55', plain,
% 8.10/8.27      (![X0 : $i, X1 : $i]:
% 8.10/8.27         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 8.10/8.27          | ~ (v1_xboole_0 @ X1)
% 8.10/8.27          | ((k3_subset_1 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1)))),
% 8.10/8.27      inference('sup-', [status(thm)], ['8', '9'])).
% 8.10/8.27  thf('56', plain,
% 8.10/8.27      (![X0 : $i]:
% 8.10/8.27         (((k3_subset_1 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ sk_B)
% 8.10/8.27            = (k3_subset_1 @ sk_C_1 @ sk_B))
% 8.10/8.27          | ((k3_subset_1 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ X0)
% 8.10/8.27              = (k4_xboole_0 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ X0))
% 8.10/8.27          | ~ (v1_xboole_0 @ X0))),
% 8.10/8.27      inference('sup-', [status(thm)], ['54', '55'])).
% 8.10/8.27  thf('57', plain,
% 8.10/8.27      ((((k3_subset_1 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ sk_B)
% 8.10/8.27          = (k3_subset_1 @ sk_C_1 @ sk_B))
% 8.10/8.27        | ~ (v1_xboole_0 @ sk_B)
% 8.10/8.27        | ((k3_subset_1 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ sk_B)
% 8.10/8.27            = (k3_subset_1 @ sk_C_1 @ sk_B)))),
% 8.10/8.27      inference('sup+', [status(thm)], ['31', '56'])).
% 8.10/8.27  thf('58', plain, ((v1_xboole_0 @ sk_B)),
% 8.10/8.27      inference('demod', [status(thm)], ['22', '23'])).
% 8.10/8.27  thf('59', plain,
% 8.10/8.27      ((((k3_subset_1 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ sk_B)
% 8.10/8.27          = (k3_subset_1 @ sk_C_1 @ sk_B))
% 8.10/8.27        | ((k3_subset_1 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ sk_B)
% 8.10/8.27            = (k3_subset_1 @ sk_C_1 @ sk_B)))),
% 8.10/8.27      inference('demod', [status(thm)], ['57', '58'])).
% 8.10/8.27  thf('60', plain,
% 8.10/8.27      (((k3_subset_1 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ sk_B)
% 8.10/8.27         = (k3_subset_1 @ sk_C_1 @ sk_B))),
% 8.10/8.27      inference('simplify', [status(thm)], ['59'])).
% 8.10/8.27  thf('61', plain,
% 8.10/8.27      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_C_1 @ sk_B)))
% 8.10/8.27        | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_C_1 @ sk_B))))),
% 8.10/8.27      inference('sup-', [status(thm)], ['48', '49'])).
% 8.10/8.27  thf(involutiveness_k3_subset_1, axiom,
% 8.10/8.27    (![A:$i,B:$i]:
% 8.10/8.27     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.10/8.27       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 8.10/8.27  thf('62', plain,
% 8.10/8.27      (![X29 : $i, X30 : $i]:
% 8.10/8.27         (((k3_subset_1 @ X30 @ (k3_subset_1 @ X30 @ X29)) = (X29))
% 8.10/8.27          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30)))),
% 8.10/8.27      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 8.10/8.27  thf('63', plain,
% 8.10/8.27      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_C_1 @ sk_B)))
% 8.10/8.27        | ((k3_subset_1 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ 
% 8.10/8.27            (k3_subset_1 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ sk_B)) = (sk_B)))),
% 8.10/8.27      inference('sup-', [status(thm)], ['61', '62'])).
% 8.10/8.27  thf('64', plain,
% 8.10/8.27      (((k3_subset_1 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ sk_B)
% 8.10/8.27         = (k3_subset_1 @ sk_C_1 @ sk_B))),
% 8.10/8.27      inference('simplify', [status(thm)], ['59'])).
% 8.10/8.27  thf(t4_subset_1, axiom,
% 8.10/8.27    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 8.10/8.27  thf('65', plain,
% 8.10/8.27      (![X31 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 8.10/8.27      inference('cnf', [status(esa)], [t4_subset_1])).
% 8.10/8.27  thf('66', plain,
% 8.10/8.27      (![X29 : $i, X30 : $i]:
% 8.10/8.27         (((k3_subset_1 @ X30 @ (k3_subset_1 @ X30 @ X29)) = (X29))
% 8.10/8.27          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30)))),
% 8.10/8.27      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 8.10/8.27  thf('67', plain,
% 8.10/8.27      (![X0 : $i]:
% 8.10/8.27         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 8.10/8.27      inference('sup-', [status(thm)], ['65', '66'])).
% 8.10/8.27  thf('68', plain,
% 8.10/8.27      (![X31 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 8.10/8.27      inference('cnf', [status(esa)], [t4_subset_1])).
% 8.10/8.27  thf('69', plain,
% 8.10/8.27      (![X27 : $i, X28 : $i]:
% 8.10/8.27         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 8.10/8.27          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 8.10/8.27      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.10/8.27  thf('70', plain,
% 8.10/8.27      (![X0 : $i]:
% 8.10/8.27         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 8.10/8.27      inference('sup-', [status(thm)], ['68', '69'])).
% 8.10/8.27  thf(t3_boole, axiom,
% 8.10/8.27    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 8.10/8.27  thf('71', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 8.10/8.27      inference('cnf', [status(esa)], [t3_boole])).
% 8.10/8.27  thf('72', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 8.10/8.27      inference('sup+', [status(thm)], ['70', '71'])).
% 8.10/8.27  thf('73', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 8.10/8.27      inference('demod', [status(thm)], ['67', '72'])).
% 8.10/8.27  thf('74', plain,
% 8.10/8.27      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_C_1 @ sk_B)))
% 8.10/8.27        | ((k1_xboole_0) = (sk_B)))),
% 8.10/8.27      inference('demod', [status(thm)], ['63', '64', '73'])).
% 8.10/8.27  thf('75', plain, (((sk_B) != (k1_xboole_0))),
% 8.10/8.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.27  thf('76', plain,
% 8.10/8.27      ((v1_xboole_0 @ (k1_zfmisc_1 @ (k3_subset_1 @ sk_C_1 @ sk_B)))),
% 8.10/8.27      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 8.10/8.27  thf('77', plain,
% 8.10/8.27      (![X25 : $i, X26 : $i]:
% 8.10/8.27         (~ (v1_xboole_0 @ X26)
% 8.10/8.27          | (m1_subset_1 @ X26 @ X25)
% 8.10/8.27          | ~ (v1_xboole_0 @ X25))),
% 8.10/8.27      inference('cnf', [status(esa)], [d2_subset_1])).
% 8.10/8.27  thf('78', plain,
% 8.10/8.27      (![X29 : $i, X30 : $i]:
% 8.10/8.27         (((k3_subset_1 @ X30 @ (k3_subset_1 @ X30 @ X29)) = (X29))
% 8.10/8.27          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30)))),
% 8.10/8.27      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 8.10/8.27  thf('79', plain,
% 8.10/8.27      (![X0 : $i, X1 : $i]:
% 8.10/8.27         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 8.10/8.27          | ~ (v1_xboole_0 @ X1)
% 8.10/8.27          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X1)) = (X1)))),
% 8.10/8.27      inference('sup-', [status(thm)], ['77', '78'])).
% 8.10/8.27  thf('80', plain,
% 8.10/8.27      (![X0 : $i]:
% 8.10/8.27         (((k3_subset_1 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ 
% 8.10/8.27            (k3_subset_1 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ X0)) = (X0))
% 8.10/8.27          | ~ (v1_xboole_0 @ X0))),
% 8.10/8.27      inference('sup-', [status(thm)], ['76', '79'])).
% 8.10/8.27  thf('81', plain,
% 8.10/8.27      ((((k3_subset_1 @ (k3_subset_1 @ sk_C_1 @ sk_B) @ 
% 8.10/8.27          (k3_subset_1 @ sk_C_1 @ sk_B)) = (sk_B))
% 8.10/8.27        | ~ (v1_xboole_0 @ sk_B))),
% 8.10/8.27      inference('sup+', [status(thm)], ['60', '80'])).
% 8.10/8.27  thf('82', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 8.10/8.27      inference('demod', [status(thm)], ['67', '72'])).
% 8.10/8.27  thf('83', plain, ((v1_xboole_0 @ sk_B)),
% 8.10/8.27      inference('demod', [status(thm)], ['22', '23'])).
% 8.10/8.27  thf('84', plain, (((k1_xboole_0) = (sk_B))),
% 8.10/8.27      inference('demod', [status(thm)], ['81', '82', '83'])).
% 8.10/8.27  thf('85', plain, (((sk_B) != (k1_xboole_0))),
% 8.10/8.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.27  thf('86', plain, ($false),
% 8.10/8.27      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 8.10/8.27  
% 8.10/8.27  % SZS output end Refutation
% 8.10/8.27  
% 8.10/8.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
