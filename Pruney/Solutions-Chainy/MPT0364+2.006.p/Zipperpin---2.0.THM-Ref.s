%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.knmmhQbP7Y

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:03 EST 2020

% Result     : Theorem 4.39s
% Output     : Refutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 267 expanded)
%              Number of leaves         :   30 (  90 expanded)
%              Depth                    :   22
%              Number of atoms          :  649 (2055 expanded)
%              Number of equality atoms :   38 (  77 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t44_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
            <=> ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
   <= ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ( r1_xboole_0 @ X18 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('9',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('11',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','12'])).

thf('14',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('16',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf('17',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','12','16'])).

thf('18',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['15','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X26 )
      | ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('23',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('24',plain,(
    r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('25',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ ( k3_tarski @ X23 ) )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('26',plain,(
    r1_tarski @ sk_C @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('27',plain,(
    ! [X24: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('28',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['26','27'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X26 )
      | ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('41',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ ( k3_tarski @ X23 ) )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('43',plain,(
    r1_tarski @ sk_B @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X24: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('45',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ( r1_xboole_0 @ X18 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('48',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( r1_xboole_0 @ X13 @ ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['43','44'])).

thf('51',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','52'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('54',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['36','55'])).

thf('57',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['19','56'])).

thf('58',plain,(
    r1_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['18','57'])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['36','55'])).

thf('60',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( r1_xboole_0 @ X13 @ ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C ) )
      | ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['43','44'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('64',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 )
      | ( r1_xboole_0 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('68',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_B ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('70',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('72',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('73',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('76',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['14','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.knmmhQbP7Y
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.39/4.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.39/4.61  % Solved by: fo/fo7.sh
% 4.39/4.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.39/4.61  % done 2188 iterations in 4.164s
% 4.39/4.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.39/4.61  % SZS output start Refutation
% 4.39/4.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.39/4.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.39/4.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 4.39/4.61  thf(sk_C_type, type, sk_C: $i).
% 4.39/4.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.39/4.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.39/4.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.39/4.61  thf(sk_B_type, type, sk_B: $i).
% 4.39/4.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 4.39/4.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.39/4.61  thf(sk_A_type, type, sk_A: $i).
% 4.39/4.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.39/4.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.39/4.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 4.39/4.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.39/4.61  thf(t44_subset_1, conjecture,
% 4.39/4.61    (![A:$i,B:$i]:
% 4.39/4.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.39/4.61       ( ![C:$i]:
% 4.39/4.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 4.39/4.61           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 4.39/4.61             ( r1_tarski @ B @ C ) ) ) ) ))).
% 4.39/4.61  thf(zf_stmt_0, negated_conjecture,
% 4.39/4.61    (~( ![A:$i,B:$i]:
% 4.39/4.61        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.39/4.61          ( ![C:$i]:
% 4.39/4.61            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 4.39/4.61              ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 4.39/4.61                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 4.39/4.61    inference('cnf.neg', [status(esa)], [t44_subset_1])).
% 4.39/4.61  thf('0', plain,
% 4.39/4.61      ((~ (r1_tarski @ sk_B @ sk_C)
% 4.39/4.61        | ~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 4.39/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.61  thf('1', plain,
% 4.39/4.61      ((~ (r1_tarski @ sk_B @ sk_C)) <= (~ ((r1_tarski @ sk_B @ sk_C)))),
% 4.39/4.61      inference('split', [status(esa)], ['0'])).
% 4.39/4.61  thf('2', plain,
% 4.39/4.61      (~ ((r1_tarski @ sk_B @ sk_C)) | 
% 4.39/4.61       ~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 4.39/4.61      inference('split', [status(esa)], ['0'])).
% 4.39/4.61  thf('3', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 4.39/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.61  thf(d5_subset_1, axiom,
% 4.39/4.61    (![A:$i,B:$i]:
% 4.39/4.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.39/4.61       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 4.39/4.61  thf('4', plain,
% 4.39/4.61      (![X28 : $i, X29 : $i]:
% 4.39/4.61         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 4.39/4.61          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 4.39/4.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 4.39/4.61  thf('5', plain,
% 4.39/4.61      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 4.39/4.61      inference('sup-', [status(thm)], ['3', '4'])).
% 4.39/4.61  thf('6', plain,
% 4.39/4.61      (((r1_tarski @ sk_B @ sk_C)
% 4.39/4.61        | (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 4.39/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.61  thf('7', plain,
% 4.39/4.61      (((r1_tarski @ sk_B @ sk_C)) <= (((r1_tarski @ sk_B @ sk_C)))),
% 4.39/4.61      inference('split', [status(esa)], ['6'])).
% 4.39/4.61  thf(t85_xboole_1, axiom,
% 4.39/4.61    (![A:$i,B:$i,C:$i]:
% 4.39/4.61     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 4.39/4.61  thf('8', plain,
% 4.39/4.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.39/4.61         (~ (r1_tarski @ X18 @ X19)
% 4.39/4.61          | (r1_xboole_0 @ X18 @ (k4_xboole_0 @ X20 @ X19)))),
% 4.39/4.61      inference('cnf', [status(esa)], [t85_xboole_1])).
% 4.39/4.61  thf('9', plain,
% 4.39/4.61      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C)))
% 4.39/4.61         <= (((r1_tarski @ sk_B @ sk_C)))),
% 4.39/4.61      inference('sup-', [status(thm)], ['7', '8'])).
% 4.39/4.61  thf('10', plain,
% 4.39/4.61      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 4.39/4.61         <= (((r1_tarski @ sk_B @ sk_C)))),
% 4.39/4.61      inference('sup+', [status(thm)], ['5', '9'])).
% 4.39/4.61  thf('11', plain,
% 4.39/4.61      ((~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 4.39/4.61         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 4.39/4.61      inference('split', [status(esa)], ['0'])).
% 4.39/4.61  thf('12', plain,
% 4.39/4.61      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 4.39/4.61       ~ ((r1_tarski @ sk_B @ sk_C))),
% 4.39/4.61      inference('sup-', [status(thm)], ['10', '11'])).
% 4.39/4.61  thf('13', plain, (~ ((r1_tarski @ sk_B @ sk_C))),
% 4.39/4.61      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 4.39/4.61  thf('14', plain, (~ (r1_tarski @ sk_B @ sk_C)),
% 4.39/4.61      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 4.39/4.61  thf('15', plain,
% 4.39/4.61      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 4.39/4.61         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 4.39/4.61      inference('split', [status(esa)], ['6'])).
% 4.39/4.61  thf('16', plain,
% 4.39/4.61      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 4.39/4.61       ((r1_tarski @ sk_B @ sk_C))),
% 4.39/4.61      inference('split', [status(esa)], ['6'])).
% 4.39/4.61  thf('17', plain, (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 4.39/4.61      inference('sat_resolution*', [status(thm)], ['2', '12', '16'])).
% 4.39/4.61  thf('18', plain, ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))),
% 4.39/4.61      inference('simpl_trail', [status(thm)], ['15', '17'])).
% 4.39/4.61  thf('19', plain,
% 4.39/4.61      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 4.39/4.61      inference('sup-', [status(thm)], ['3', '4'])).
% 4.39/4.61  thf('20', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 4.39/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.61  thf(d2_subset_1, axiom,
% 4.39/4.61    (![A:$i,B:$i]:
% 4.39/4.61     ( ( ( v1_xboole_0 @ A ) =>
% 4.39/4.61         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 4.39/4.61       ( ( ~( v1_xboole_0 @ A ) ) =>
% 4.39/4.61         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 4.39/4.61  thf('21', plain,
% 4.39/4.61      (![X25 : $i, X26 : $i]:
% 4.39/4.61         (~ (m1_subset_1 @ X25 @ X26)
% 4.39/4.61          | (r2_hidden @ X25 @ X26)
% 4.39/4.61          | (v1_xboole_0 @ X26))),
% 4.39/4.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 4.39/4.61  thf('22', plain,
% 4.39/4.61      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 4.39/4.61        | (r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A)))),
% 4.39/4.61      inference('sup-', [status(thm)], ['20', '21'])).
% 4.39/4.61  thf(fc1_subset_1, axiom,
% 4.39/4.61    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 4.39/4.61  thf('23', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 4.39/4.61      inference('cnf', [status(esa)], [fc1_subset_1])).
% 4.39/4.61  thf('24', plain, ((r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 4.39/4.61      inference('clc', [status(thm)], ['22', '23'])).
% 4.39/4.61  thf(l49_zfmisc_1, axiom,
% 4.39/4.61    (![A:$i,B:$i]:
% 4.39/4.61     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 4.39/4.61  thf('25', plain,
% 4.39/4.61      (![X22 : $i, X23 : $i]:
% 4.39/4.61         ((r1_tarski @ X22 @ (k3_tarski @ X23)) | ~ (r2_hidden @ X22 @ X23))),
% 4.39/4.61      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 4.39/4.61  thf('26', plain, ((r1_tarski @ sk_C @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 4.39/4.61      inference('sup-', [status(thm)], ['24', '25'])).
% 4.39/4.61  thf(t99_zfmisc_1, axiom,
% 4.39/4.61    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 4.39/4.61  thf('27', plain, (![X24 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X24)) = (X24))),
% 4.39/4.61      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 4.39/4.61  thf('28', plain, ((r1_tarski @ sk_C @ sk_A)),
% 4.39/4.61      inference('demod', [status(thm)], ['26', '27'])).
% 4.39/4.61  thf(l32_xboole_1, axiom,
% 4.39/4.61    (![A:$i,B:$i]:
% 4.39/4.61     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.39/4.61  thf('29', plain,
% 4.39/4.61      (![X2 : $i, X4 : $i]:
% 4.39/4.61         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 4.39/4.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.39/4.61  thf('30', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 4.39/4.61      inference('sup-', [status(thm)], ['28', '29'])).
% 4.39/4.61  thf(t48_xboole_1, axiom,
% 4.39/4.61    (![A:$i,B:$i]:
% 4.39/4.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.39/4.61  thf('31', plain,
% 4.39/4.61      (![X7 : $i, X8 : $i]:
% 4.39/4.61         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 4.39/4.61           = (k3_xboole_0 @ X7 @ X8))),
% 4.39/4.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.39/4.61  thf('32', plain,
% 4.39/4.61      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_A))),
% 4.39/4.61      inference('sup+', [status(thm)], ['30', '31'])).
% 4.39/4.61  thf(commutativity_k3_xboole_0, axiom,
% 4.39/4.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.39/4.61  thf('33', plain,
% 4.39/4.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.39/4.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.39/4.61  thf(t100_xboole_1, axiom,
% 4.39/4.61    (![A:$i,B:$i]:
% 4.39/4.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 4.39/4.61  thf('34', plain,
% 4.39/4.61      (![X5 : $i, X6 : $i]:
% 4.39/4.61         ((k4_xboole_0 @ X5 @ X6)
% 4.39/4.61           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 4.39/4.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.39/4.61  thf('35', plain,
% 4.39/4.61      (![X0 : $i, X1 : $i]:
% 4.39/4.61         ((k4_xboole_0 @ X0 @ X1)
% 4.39/4.61           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 4.39/4.61      inference('sup+', [status(thm)], ['33', '34'])).
% 4.39/4.61  thf('36', plain,
% 4.39/4.61      (((k4_xboole_0 @ sk_A @ sk_C)
% 4.39/4.61         = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ k1_xboole_0)))),
% 4.39/4.61      inference('sup+', [status(thm)], ['32', '35'])).
% 4.39/4.61  thf('37', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 4.39/4.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.39/4.61  thf('38', plain,
% 4.39/4.61      (![X25 : $i, X26 : $i]:
% 4.39/4.61         (~ (m1_subset_1 @ X25 @ X26)
% 4.39/4.61          | (r2_hidden @ X25 @ X26)
% 4.39/4.61          | (v1_xboole_0 @ X26))),
% 4.39/4.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 4.39/4.61  thf('39', plain,
% 4.39/4.61      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 4.39/4.61        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 4.39/4.61      inference('sup-', [status(thm)], ['37', '38'])).
% 4.39/4.61  thf('40', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 4.39/4.61      inference('cnf', [status(esa)], [fc1_subset_1])).
% 4.39/4.61  thf('41', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 4.39/4.61      inference('clc', [status(thm)], ['39', '40'])).
% 4.39/4.61  thf('42', plain,
% 4.39/4.61      (![X22 : $i, X23 : $i]:
% 4.39/4.61         ((r1_tarski @ X22 @ (k3_tarski @ X23)) | ~ (r2_hidden @ X22 @ X23))),
% 4.39/4.61      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 4.39/4.61  thf('43', plain, ((r1_tarski @ sk_B @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 4.39/4.61      inference('sup-', [status(thm)], ['41', '42'])).
% 4.39/4.61  thf('44', plain, (![X24 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X24)) = (X24))),
% 4.39/4.61      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 4.39/4.61  thf('45', plain, ((r1_tarski @ sk_B @ sk_A)),
% 4.39/4.61      inference('demod', [status(thm)], ['43', '44'])).
% 4.39/4.61  thf('46', plain,
% 4.39/4.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.39/4.61         (~ (r1_tarski @ X18 @ X19)
% 4.39/4.61          | (r1_xboole_0 @ X18 @ (k4_xboole_0 @ X20 @ X19)))),
% 4.39/4.61      inference('cnf', [status(esa)], [t85_xboole_1])).
% 4.39/4.61  thf('47', plain,
% 4.39/4.61      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A))),
% 4.39/4.61      inference('sup-', [status(thm)], ['45', '46'])).
% 4.39/4.61  thf(t81_xboole_1, axiom,
% 4.39/4.61    (![A:$i,B:$i,C:$i]:
% 4.39/4.61     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 4.39/4.61       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 4.39/4.61  thf('48', plain,
% 4.39/4.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.39/4.61         ((r1_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 4.39/4.61          | ~ (r1_xboole_0 @ X13 @ (k4_xboole_0 @ X12 @ X14)))),
% 4.39/4.61      inference('cnf', [status(esa)], [t81_xboole_1])).
% 4.39/4.61  thf('49', plain,
% 4.39/4.61      (![X0 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_A))),
% 4.39/4.61      inference('sup-', [status(thm)], ['47', '48'])).
% 4.39/4.61  thf('50', plain, ((r1_tarski @ sk_B @ sk_A)),
% 4.39/4.61      inference('demod', [status(thm)], ['43', '44'])).
% 4.39/4.61  thf('51', plain,
% 4.39/4.61      (![X2 : $i, X4 : $i]:
% 4.39/4.61         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 4.39/4.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.39/4.61  thf('52', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 4.39/4.61      inference('sup-', [status(thm)], ['50', '51'])).
% 4.39/4.61  thf('53', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 4.39/4.61      inference('demod', [status(thm)], ['49', '52'])).
% 4.39/4.61  thf(t83_xboole_1, axiom,
% 4.39/4.61    (![A:$i,B:$i]:
% 4.39/4.61     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.39/4.61  thf('54', plain,
% 4.39/4.61      (![X15 : $i, X16 : $i]:
% 4.39/4.61         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 4.39/4.61      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.39/4.61  thf('55', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 4.39/4.61      inference('sup-', [status(thm)], ['53', '54'])).
% 4.39/4.61  thf('56', plain,
% 4.39/4.61      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 4.39/4.61      inference('demod', [status(thm)], ['36', '55'])).
% 4.39/4.61  thf('57', plain,
% 4.39/4.61      (((k3_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 4.39/4.61      inference('sup+', [status(thm)], ['19', '56'])).
% 4.39/4.61  thf('58', plain, ((r1_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C))),
% 4.39/4.61      inference('demod', [status(thm)], ['18', '57'])).
% 4.39/4.61  thf('59', plain,
% 4.39/4.61      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 4.39/4.61      inference('demod', [status(thm)], ['36', '55'])).
% 4.39/4.61  thf('60', plain,
% 4.39/4.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.39/4.61         ((r1_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 4.39/4.61          | ~ (r1_xboole_0 @ X13 @ (k4_xboole_0 @ X12 @ X14)))),
% 4.39/4.61      inference('cnf', [status(esa)], [t81_xboole_1])).
% 4.39/4.61  thf('61', plain,
% 4.39/4.61      (![X0 : $i]:
% 4.39/4.61         (~ (r1_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C))
% 4.39/4.61          | (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C)))),
% 4.39/4.61      inference('sup-', [status(thm)], ['59', '60'])).
% 4.39/4.61  thf('62', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 4.39/4.61      inference('sup-', [status(thm)], ['58', '61'])).
% 4.39/4.61  thf('63', plain, ((r1_tarski @ sk_B @ sk_A)),
% 4.39/4.61      inference('demod', [status(thm)], ['43', '44'])).
% 4.39/4.61  thf(t63_xboole_1, axiom,
% 4.39/4.61    (![A:$i,B:$i,C:$i]:
% 4.39/4.61     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 4.39/4.61       ( r1_xboole_0 @ A @ C ) ))).
% 4.39/4.61  thf('64', plain,
% 4.39/4.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.39/4.61         (~ (r1_tarski @ X9 @ X10)
% 4.39/4.61          | ~ (r1_xboole_0 @ X10 @ X11)
% 4.39/4.61          | (r1_xboole_0 @ X9 @ X11))),
% 4.39/4.61      inference('cnf', [status(esa)], [t63_xboole_1])).
% 4.39/4.61  thf('65', plain,
% 4.39/4.61      (![X0 : $i]: ((r1_xboole_0 @ sk_B @ X0) | ~ (r1_xboole_0 @ sk_A @ X0))),
% 4.39/4.61      inference('sup-', [status(thm)], ['63', '64'])).
% 4.39/4.61  thf('66', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C))),
% 4.39/4.61      inference('sup-', [status(thm)], ['62', '65'])).
% 4.39/4.61  thf('67', plain,
% 4.39/4.61      (![X15 : $i, X16 : $i]:
% 4.39/4.61         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 4.39/4.61      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.39/4.61  thf('68', plain,
% 4.39/4.61      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_B))),
% 4.39/4.61      inference('sup-', [status(thm)], ['66', '67'])).
% 4.39/4.61  thf('69', plain,
% 4.39/4.61      (![X7 : $i, X8 : $i]:
% 4.39/4.61         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 4.39/4.61           = (k3_xboole_0 @ X7 @ X8))),
% 4.39/4.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.39/4.61  thf('70', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 4.39/4.61      inference('demod', [status(thm)], ['68', '69'])).
% 4.39/4.61  thf('71', plain,
% 4.39/4.61      (![X5 : $i, X6 : $i]:
% 4.39/4.61         ((k4_xboole_0 @ X5 @ X6)
% 4.39/4.61           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 4.39/4.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.39/4.61  thf('72', plain,
% 4.39/4.61      (((k4_xboole_0 @ sk_B @ sk_C) = (k5_xboole_0 @ sk_B @ sk_B))),
% 4.39/4.61      inference('sup+', [status(thm)], ['70', '71'])).
% 4.39/4.61  thf(t92_xboole_1, axiom,
% 4.39/4.61    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 4.39/4.61  thf('73', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 4.39/4.61      inference('cnf', [status(esa)], [t92_xboole_1])).
% 4.39/4.61  thf('74', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 4.39/4.61      inference('demod', [status(thm)], ['72', '73'])).
% 4.39/4.61  thf('75', plain,
% 4.39/4.61      (![X2 : $i, X3 : $i]:
% 4.39/4.61         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 4.39/4.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.39/4.61  thf('76', plain,
% 4.39/4.61      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_B @ sk_C))),
% 4.39/4.61      inference('sup-', [status(thm)], ['74', '75'])).
% 4.39/4.61  thf('77', plain, ((r1_tarski @ sk_B @ sk_C)),
% 4.39/4.61      inference('simplify', [status(thm)], ['76'])).
% 4.39/4.61  thf('78', plain, ($false), inference('demod', [status(thm)], ['14', '77'])).
% 4.39/4.61  
% 4.39/4.61  % SZS output end Refutation
% 4.39/4.61  
% 4.39/4.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
