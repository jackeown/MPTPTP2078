%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tOdVy8fL1L

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:00 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 274 expanded)
%              Number of leaves         :   29 (  95 expanded)
%              Depth                    :   22
%              Number of atoms          :  805 (2132 expanded)
%              Number of equality atoms :   38 (  88 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t43_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_xboole_0 @ B @ C )
            <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X24: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('6',plain,(
    r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ ( k3_tarski @ X17 ) )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('8',plain,(
    r1_tarski @ sk_C @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X18: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('10',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['8','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X24: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('21',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ ( k3_tarski @ X17 ) )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('23',plain,(
    r1_tarski @ sk_B @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X18: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('25',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['26'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X12 @ X14 )
      | ( r1_tarski @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['16','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('36',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['26'])).

thf('41',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['23','24'])).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['8','9'])).

thf('49',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('51',plain,(
    r1_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('53',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['26'])).

thf('54',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('55',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
      = sk_B )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('57',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('58',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('59',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(t84_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ A @ C )
        & ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('60',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( r1_xboole_0 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t84_xboole_1])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
        | ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
        | ( r1_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('62',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
        | ( r1_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C ) )
        | ( r1_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','63'])).

thf('65',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','64'])).

thf('66',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X12 @ X14 )
      | ( r1_tarski @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ ( k4_xboole_0 @ X0 @ sk_B ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r1_tarski @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','67'])).

thf('69',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('71',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_tarski @ sk_C @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('74',plain,
    ( ( ( k3_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_A @ sk_B ) )
      = sk_C )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('76',plain,
    ( ( ( k4_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_C @ sk_C ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('78',plain,
    ( ( ( k4_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( r1_xboole_0 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t84_xboole_1])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
        | ~ ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) )
        | ( r1_xboole_0 @ X0 @ sk_C ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) )
        | ( r1_xboole_0 @ X0 @ sk_C ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','82'])).

thf('84',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('85',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tOdVy8fL1L
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:24:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.36/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.63  % Solved by: fo/fo7.sh
% 0.36/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.63  % done 210 iterations in 0.153s
% 0.36/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.63  % SZS output start Refutation
% 0.36/0.63  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.63  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.63  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.36/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.63  thf(t43_subset_1, conjecture,
% 0.36/0.63    (![A:$i,B:$i]:
% 0.36/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.63       ( ![C:$i]:
% 0.36/0.63         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.63           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.36/0.63             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.36/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.63    (~( ![A:$i,B:$i]:
% 0.36/0.63        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.63          ( ![C:$i]:
% 0.36/0.63            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.63              ( ( r1_xboole_0 @ B @ C ) <=>
% 0.36/0.63                ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.36/0.63    inference('cnf.neg', [status(esa)], [t43_subset_1])).
% 0.36/0.63  thf('0', plain,
% 0.36/0.63      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))
% 0.36/0.63        | ~ (r1_xboole_0 @ sk_B @ sk_C))),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf('1', plain,
% 0.36/0.63      (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.36/0.63       ~ ((r1_xboole_0 @ sk_B @ sk_C))),
% 0.36/0.63      inference('split', [status(esa)], ['0'])).
% 0.36/0.63  thf('2', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf(d2_subset_1, axiom,
% 0.36/0.63    (![A:$i,B:$i]:
% 0.36/0.63     ( ( ( v1_xboole_0 @ A ) =>
% 0.36/0.63         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.36/0.63       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.63         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.63  thf('3', plain,
% 0.36/0.63      (![X19 : $i, X20 : $i]:
% 0.36/0.63         (~ (m1_subset_1 @ X19 @ X20)
% 0.36/0.63          | (r2_hidden @ X19 @ X20)
% 0.36/0.63          | (v1_xboole_0 @ X20))),
% 0.36/0.63      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.36/0.63  thf('4', plain,
% 0.36/0.63      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.36/0.63        | (r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.63  thf(fc1_subset_1, axiom,
% 0.36/0.63    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.63  thf('5', plain, (![X24 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 0.36/0.63      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.36/0.63  thf('6', plain, ((r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.63      inference('clc', [status(thm)], ['4', '5'])).
% 0.36/0.63  thf(l49_zfmisc_1, axiom,
% 0.36/0.63    (![A:$i,B:$i]:
% 0.36/0.63     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.36/0.63  thf('7', plain,
% 0.36/0.63      (![X16 : $i, X17 : $i]:
% 0.36/0.63         ((r1_tarski @ X16 @ (k3_tarski @ X17)) | ~ (r2_hidden @ X16 @ X17))),
% 0.36/0.63      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.36/0.63  thf('8', plain, ((r1_tarski @ sk_C @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.63      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.63  thf(t99_zfmisc_1, axiom,
% 0.36/0.63    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.36/0.63  thf('9', plain, (![X18 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X18)) = (X18))),
% 0.36/0.63      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.36/0.63  thf('10', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.36/0.63      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.63  thf(t28_xboole_1, axiom,
% 0.36/0.63    (![A:$i,B:$i]:
% 0.36/0.63     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.63  thf('11', plain,
% 0.36/0.63      (![X6 : $i, X7 : $i]:
% 0.36/0.63         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.36/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.63  thf('12', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.36/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.36/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.36/0.63  thf('13', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.63  thf(t100_xboole_1, axiom,
% 0.36/0.63    (![A:$i,B:$i]:
% 0.36/0.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.63  thf('14', plain,
% 0.36/0.63      (![X4 : $i, X5 : $i]:
% 0.36/0.63         ((k4_xboole_0 @ X4 @ X5)
% 0.36/0.63           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.63  thf('15', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]:
% 0.36/0.63         ((k4_xboole_0 @ X0 @ X1)
% 0.36/0.63           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['13', '14'])).
% 0.36/0.63  thf('16', plain,
% 0.36/0.63      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.36/0.63      inference('sup+', [status(thm)], ['12', '15'])).
% 0.36/0.63  thf('17', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf('18', plain,
% 0.36/0.63      (![X19 : $i, X20 : $i]:
% 0.36/0.63         (~ (m1_subset_1 @ X19 @ X20)
% 0.36/0.63          | (r2_hidden @ X19 @ X20)
% 0.36/0.63          | (v1_xboole_0 @ X20))),
% 0.36/0.63      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.36/0.63  thf('19', plain,
% 0.36/0.63      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.36/0.63        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.63  thf('20', plain, (![X24 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 0.36/0.63      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.36/0.63  thf('21', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.63      inference('clc', [status(thm)], ['19', '20'])).
% 0.36/0.63  thf('22', plain,
% 0.36/0.63      (![X16 : $i, X17 : $i]:
% 0.36/0.63         ((r1_tarski @ X16 @ (k3_tarski @ X17)) | ~ (r2_hidden @ X16 @ X17))),
% 0.36/0.63      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.36/0.63  thf('23', plain, ((r1_tarski @ sk_B @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.36/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.63  thf('24', plain, (![X18 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X18)) = (X18))),
% 0.36/0.63      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.36/0.63  thf('25', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.36/0.63      inference('demod', [status(thm)], ['23', '24'])).
% 0.36/0.63  thf('26', plain,
% 0.36/0.63      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))
% 0.36/0.63        | (r1_xboole_0 @ sk_B @ sk_C))),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf('27', plain,
% 0.36/0.63      (((r1_xboole_0 @ sk_B @ sk_C)) <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.36/0.63      inference('split', [status(esa)], ['26'])).
% 0.36/0.63  thf(t86_xboole_1, axiom,
% 0.36/0.63    (![A:$i,B:$i,C:$i]:
% 0.36/0.63     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.36/0.63       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.36/0.63  thf('28', plain,
% 0.36/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.63         (~ (r1_tarski @ X12 @ X13)
% 0.36/0.63          | ~ (r1_xboole_0 @ X12 @ X14)
% 0.36/0.63          | (r1_tarski @ X12 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.36/0.63  thf('29', plain,
% 0.36/0.63      ((![X0 : $i]:
% 0.36/0.63          ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))
% 0.36/0.63           | ~ (r1_tarski @ sk_B @ X0)))
% 0.36/0.63         <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.36/0.63      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.63  thf('30', plain,
% 0.36/0.63      (((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))
% 0.36/0.63         <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.36/0.63      inference('sup-', [status(thm)], ['25', '29'])).
% 0.36/0.63  thf('31', plain,
% 0.36/0.63      (((r1_tarski @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C)))
% 0.36/0.63         <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['16', '30'])).
% 0.36/0.63  thf('32', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf(d5_subset_1, axiom,
% 0.36/0.63    (![A:$i,B:$i]:
% 0.36/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.63       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.36/0.63  thf('33', plain,
% 0.36/0.63      (![X22 : $i, X23 : $i]:
% 0.36/0.63         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 0.36/0.63          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.36/0.63      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.63  thf('34', plain,
% 0.36/0.63      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.36/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.36/0.63  thf('35', plain,
% 0.36/0.63      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.36/0.63      inference('sup+', [status(thm)], ['12', '15'])).
% 0.36/0.63  thf('36', plain,
% 0.36/0.63      (((k3_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.36/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.36/0.63  thf('37', plain,
% 0.36/0.63      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.36/0.63         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.36/0.63      inference('split', [status(esa)], ['0'])).
% 0.36/0.63  thf('38', plain,
% 0.36/0.63      ((~ (r1_tarski @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C)))
% 0.36/0.63         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.36/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.63  thf('39', plain,
% 0.36/0.63      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.36/0.63       ~ ((r1_xboole_0 @ sk_B @ sk_C))),
% 0.36/0.63      inference('sup-', [status(thm)], ['31', '38'])).
% 0.36/0.63  thf('40', plain,
% 0.36/0.63      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.36/0.63       ((r1_xboole_0 @ sk_B @ sk_C))),
% 0.36/0.63      inference('split', [status(esa)], ['26'])).
% 0.36/0.63  thf('41', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.36/0.63      inference('demod', [status(thm)], ['23', '24'])).
% 0.36/0.63  thf('42', plain,
% 0.36/0.63      (![X6 : $i, X7 : $i]:
% 0.36/0.63         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.36/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.63  thf('43', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.36/0.63      inference('sup-', [status(thm)], ['41', '42'])).
% 0.36/0.63  thf('44', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.63  thf(l97_xboole_1, axiom,
% 0.36/0.63    (![A:$i,B:$i]:
% 0.36/0.63     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.36/0.63  thf('45', plain,
% 0.36/0.63      (![X2 : $i, X3 : $i]:
% 0.36/0.63         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ (k5_xboole_0 @ X2 @ X3))),
% 0.36/0.63      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.36/0.63  thf('46', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]:
% 0.36/0.63         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1))),
% 0.36/0.63      inference('sup+', [status(thm)], ['44', '45'])).
% 0.36/0.63  thf('47', plain, ((r1_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.63      inference('sup+', [status(thm)], ['43', '46'])).
% 0.36/0.63  thf('48', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.36/0.63      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.63  thf('49', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.36/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.63  thf('50', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]:
% 0.36/0.63         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1))),
% 0.36/0.63      inference('sup+', [status(thm)], ['44', '45'])).
% 0.36/0.63  thf('51', plain, ((r1_xboole_0 @ sk_C @ (k5_xboole_0 @ sk_A @ sk_C))),
% 0.36/0.63      inference('sup+', [status(thm)], ['49', '50'])).
% 0.36/0.63  thf('52', plain,
% 0.36/0.63      (((k3_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.36/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.36/0.63  thf('53', plain,
% 0.36/0.63      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.36/0.63         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.36/0.63      inference('split', [status(esa)], ['26'])).
% 0.36/0.63  thf('54', plain,
% 0.36/0.63      (![X6 : $i, X7 : $i]:
% 0.36/0.63         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.36/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.63  thf('55', plain,
% 0.36/0.63      ((((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_B)))
% 0.36/0.63         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.36/0.63      inference('sup-', [status(thm)], ['53', '54'])).
% 0.36/0.63  thf('56', plain,
% 0.36/0.63      (![X4 : $i, X5 : $i]:
% 0.36/0.63         ((k4_xboole_0 @ X4 @ X5)
% 0.36/0.63           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.63  thf('57', plain,
% 0.36/0.63      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))
% 0.36/0.63          = (k5_xboole_0 @ sk_B @ sk_B)))
% 0.36/0.63         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.36/0.63      inference('sup+', [status(thm)], ['55', '56'])).
% 0.36/0.63  thf(t92_xboole_1, axiom,
% 0.36/0.63    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.63  thf('58', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.36/0.63      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.36/0.63  thf('59', plain,
% 0.36/0.63      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)) = (k1_xboole_0)))
% 0.36/0.63         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.36/0.63      inference('demod', [status(thm)], ['57', '58'])).
% 0.36/0.63  thf(t84_xboole_1, axiom,
% 0.36/0.63    (![A:$i,B:$i,C:$i]:
% 0.36/0.63     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ C ) & 
% 0.36/0.63          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ))).
% 0.36/0.63  thf('60', plain,
% 0.36/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.63         ((r1_xboole_0 @ X9 @ X10)
% 0.36/0.63          | ~ (r1_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 0.36/0.63          | ~ (r1_xboole_0 @ X9 @ X11))),
% 0.36/0.63      inference('cnf', [status(esa)], [t84_xboole_1])).
% 0.36/0.63  thf('61', plain,
% 0.36/0.63      ((![X0 : $i]:
% 0.36/0.63          (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 0.36/0.63           | ~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.36/0.63           | (r1_xboole_0 @ X0 @ sk_B)))
% 0.36/0.63         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.36/0.63      inference('sup-', [status(thm)], ['59', '60'])).
% 0.36/0.63  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.36/0.63  thf('62', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.36/0.63      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.36/0.63  thf('63', plain,
% 0.36/0.63      ((![X0 : $i]:
% 0.36/0.63          (~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.36/0.63           | (r1_xboole_0 @ X0 @ sk_B)))
% 0.36/0.63         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.36/0.63      inference('demod', [status(thm)], ['61', '62'])).
% 0.36/0.63  thf('64', plain,
% 0.36/0.63      ((![X0 : $i]:
% 0.36/0.63          (~ (r1_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C))
% 0.36/0.63           | (r1_xboole_0 @ X0 @ sk_B)))
% 0.36/0.63         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.36/0.63      inference('sup-', [status(thm)], ['52', '63'])).
% 0.36/0.63  thf('65', plain,
% 0.36/0.63      (((r1_xboole_0 @ sk_C @ sk_B))
% 0.36/0.63         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.36/0.63      inference('sup-', [status(thm)], ['51', '64'])).
% 0.36/0.63  thf('66', plain,
% 0.36/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.63         (~ (r1_tarski @ X12 @ X13)
% 0.36/0.63          | ~ (r1_xboole_0 @ X12 @ X14)
% 0.36/0.63          | (r1_tarski @ X12 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.36/0.63  thf('67', plain,
% 0.36/0.63      ((![X0 : $i]:
% 0.36/0.63          ((r1_tarski @ sk_C @ (k4_xboole_0 @ X0 @ sk_B))
% 0.36/0.63           | ~ (r1_tarski @ sk_C @ X0)))
% 0.36/0.63         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.36/0.63      inference('sup-', [status(thm)], ['65', '66'])).
% 0.36/0.63  thf('68', plain,
% 0.36/0.63      (((r1_tarski @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.36/0.63         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.36/0.63      inference('sup-', [status(thm)], ['48', '67'])).
% 0.36/0.63  thf('69', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.36/0.63      inference('sup-', [status(thm)], ['41', '42'])).
% 0.36/0.63  thf('70', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]:
% 0.36/0.63         ((k4_xboole_0 @ X0 @ X1)
% 0.36/0.63           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['13', '14'])).
% 0.36/0.63  thf('71', plain,
% 0.36/0.63      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.63      inference('sup+', [status(thm)], ['69', '70'])).
% 0.36/0.63  thf('72', plain,
% 0.36/0.63      (((r1_tarski @ sk_C @ (k5_xboole_0 @ sk_A @ sk_B)))
% 0.36/0.63         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.36/0.63      inference('demod', [status(thm)], ['68', '71'])).
% 0.36/0.63  thf('73', plain,
% 0.36/0.63      (![X6 : $i, X7 : $i]:
% 0.36/0.63         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.36/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.63  thf('74', plain,
% 0.36/0.63      ((((k3_xboole_0 @ sk_C @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_C)))
% 0.36/0.63         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.36/0.63      inference('sup-', [status(thm)], ['72', '73'])).
% 0.36/0.63  thf('75', plain,
% 0.36/0.63      (![X4 : $i, X5 : $i]:
% 0.36/0.63         ((k4_xboole_0 @ X4 @ X5)
% 0.36/0.63           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.63  thf('76', plain,
% 0.36/0.63      ((((k4_xboole_0 @ sk_C @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.36/0.63          = (k5_xboole_0 @ sk_C @ sk_C)))
% 0.36/0.63         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.36/0.63      inference('sup+', [status(thm)], ['74', '75'])).
% 0.36/0.63  thf('77', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.36/0.63      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.36/0.63  thf('78', plain,
% 0.36/0.63      ((((k4_xboole_0 @ sk_C @ (k5_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0)))
% 0.36/0.63         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.36/0.63      inference('demod', [status(thm)], ['76', '77'])).
% 0.36/0.63  thf('79', plain,
% 0.36/0.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.63         ((r1_xboole_0 @ X9 @ X10)
% 0.36/0.63          | ~ (r1_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 0.36/0.63          | ~ (r1_xboole_0 @ X9 @ X11))),
% 0.36/0.63      inference('cnf', [status(esa)], [t84_xboole_1])).
% 0.36/0.63  thf('80', plain,
% 0.36/0.63      ((![X0 : $i]:
% 0.36/0.63          (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 0.36/0.63           | ~ (r1_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.36/0.63           | (r1_xboole_0 @ X0 @ sk_C)))
% 0.36/0.63         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.36/0.63      inference('sup-', [status(thm)], ['78', '79'])).
% 0.36/0.63  thf('81', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.36/0.63      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.36/0.63  thf('82', plain,
% 0.36/0.63      ((![X0 : $i]:
% 0.36/0.63          (~ (r1_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.36/0.63           | (r1_xboole_0 @ X0 @ sk_C)))
% 0.36/0.63         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.36/0.63      inference('demod', [status(thm)], ['80', '81'])).
% 0.36/0.63  thf('83', plain,
% 0.36/0.63      (((r1_xboole_0 @ sk_B @ sk_C))
% 0.36/0.63         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.36/0.63      inference('sup-', [status(thm)], ['47', '82'])).
% 0.36/0.63  thf('84', plain,
% 0.36/0.63      ((~ (r1_xboole_0 @ sk_B @ sk_C)) <= (~ ((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.36/0.63      inference('split', [status(esa)], ['0'])).
% 0.36/0.63  thf('85', plain,
% 0.36/0.63      (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.36/0.63       ((r1_xboole_0 @ sk_B @ sk_C))),
% 0.36/0.63      inference('sup-', [status(thm)], ['83', '84'])).
% 0.36/0.63  thf('86', plain, ($false),
% 0.36/0.63      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '85'])).
% 0.36/0.63  
% 0.36/0.63  % SZS output end Refutation
% 0.36/0.63  
% 0.49/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
