%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Sp9l7WAAC6

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:00 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 206 expanded)
%              Number of leaves         :   27 (  72 expanded)
%              Depth                    :   15
%              Number of atoms          :  599 (1600 expanded)
%              Number of equality atoms :   32 (  68 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X25: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('6',plain,(
    r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ ( k3_tarski @ X18 ) )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('8',plain,(
    r1_tarski @ sk_C @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X19: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X19 ) )
      = X19 ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X25: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('21',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ ( k3_tarski @ X18 ) )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('23',plain,(
    r1_tarski @ sk_B @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X19: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X19 ) )
      = X19 ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ X16 )
      | ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
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
    inference('sup+',[status(thm)],['34','35'])).

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

thf('41',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['26'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('51',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_xboole_0 @ X11 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('52',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) ) )
        = sk_B )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C ) ) )
        = sk_B )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_C )
      = sk_B )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['49','56'])).

thf('58',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k4_xboole_0 @ X8 @ X10 )
       != X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('59',plain,
    ( ( ( sk_B != sk_B )
      | ( r1_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('62',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) )
    | ( r1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Sp9l7WAAC6
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 229 iterations in 0.138s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.59  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.41/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.41/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(t43_subset_1, conjecture,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.59       ( ![C:$i]:
% 0.41/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.59           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.41/0.59             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i,B:$i]:
% 0.41/0.59        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.59          ( ![C:$i]:
% 0.41/0.59            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.59              ( ( r1_xboole_0 @ B @ C ) <=>
% 0.41/0.59                ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t43_subset_1])).
% 0.41/0.59  thf('0', plain,
% 0.41/0.59      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))
% 0.41/0.59        | ~ (r1_xboole_0 @ sk_B @ sk_C))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.41/0.59       ~ ((r1_xboole_0 @ sk_B @ sk_C))),
% 0.41/0.59      inference('split', [status(esa)], ['0'])).
% 0.41/0.59  thf('2', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(d2_subset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( v1_xboole_0 @ A ) =>
% 0.41/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.41/0.59       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      (![X20 : $i, X21 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X20 @ X21)
% 0.41/0.59          | (r2_hidden @ X20 @ X21)
% 0.41/0.59          | (v1_xboole_0 @ X21))),
% 0.41/0.59      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.41/0.59        | (r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.59  thf(fc1_subset_1, axiom,
% 0.41/0.59    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.41/0.59  thf('5', plain, (![X25 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X25))),
% 0.41/0.59      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.41/0.59  thf('6', plain, ((r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.59      inference('clc', [status(thm)], ['4', '5'])).
% 0.41/0.59  thf(l49_zfmisc_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      (![X17 : $i, X18 : $i]:
% 0.41/0.59         ((r1_tarski @ X17 @ (k3_tarski @ X18)) | ~ (r2_hidden @ X17 @ X18))),
% 0.41/0.59      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.41/0.59  thf('8', plain, ((r1_tarski @ sk_C @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.59  thf(t99_zfmisc_1, axiom,
% 0.41/0.59    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.41/0.59  thf('9', plain, (![X19 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X19)) = (X19))),
% 0.41/0.59      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.41/0.59  thf('10', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.41/0.59      inference('demod', [status(thm)], ['8', '9'])).
% 0.41/0.59  thf(t28_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      (![X6 : $i, X7 : $i]:
% 0.41/0.59         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.41/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.59  thf('12', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.41/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.41/0.59  thf(commutativity_k3_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.41/0.59  thf('13', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.59  thf(t100_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      (![X4 : $i, X5 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X4 @ X5)
% 0.41/0.59           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.41/0.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['13', '14'])).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.41/0.59      inference('sup+', [status(thm)], ['12', '15'])).
% 0.41/0.59  thf('17', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (![X20 : $i, X21 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X20 @ X21)
% 0.41/0.59          | (r2_hidden @ X20 @ X21)
% 0.41/0.59          | (v1_xboole_0 @ X21))),
% 0.41/0.59      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.41/0.59  thf('19', plain,
% 0.41/0.59      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.41/0.59        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.59  thf('20', plain, (![X25 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X25))),
% 0.41/0.59      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.41/0.59  thf('21', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.59      inference('clc', [status(thm)], ['19', '20'])).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      (![X17 : $i, X18 : $i]:
% 0.41/0.59         ((r1_tarski @ X17 @ (k3_tarski @ X18)) | ~ (r2_hidden @ X17 @ X18))),
% 0.41/0.59      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.41/0.59  thf('23', plain, ((r1_tarski @ sk_B @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.59  thf('24', plain, (![X19 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X19)) = (X19))),
% 0.41/0.59      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.41/0.59  thf('25', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.41/0.59      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.59  thf('26', plain,
% 0.41/0.59      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))
% 0.41/0.59        | (r1_xboole_0 @ sk_B @ sk_C))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('27', plain,
% 0.41/0.59      (((r1_xboole_0 @ sk_B @ sk_C)) <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.41/0.59      inference('split', [status(esa)], ['26'])).
% 0.41/0.59  thf(t86_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.41/0.59       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.41/0.59  thf('28', plain,
% 0.41/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.59         (~ (r1_tarski @ X14 @ X15)
% 0.41/0.59          | ~ (r1_xboole_0 @ X14 @ X16)
% 0.41/0.59          | (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X16)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.41/0.59  thf('29', plain,
% 0.41/0.59      ((![X0 : $i]:
% 0.41/0.59          ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))
% 0.41/0.59           | ~ (r1_tarski @ sk_B @ X0)))
% 0.41/0.59         <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.41/0.59  thf('30', plain,
% 0.41/0.59      (((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))
% 0.41/0.59         <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['25', '29'])).
% 0.41/0.59  thf('31', plain,
% 0.41/0.59      (((r1_tarski @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C)))
% 0.41/0.59         <= (((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['16', '30'])).
% 0.41/0.59  thf('32', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(d5_subset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.59       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.41/0.59  thf('33', plain,
% 0.41/0.59      (![X23 : $i, X24 : $i]:
% 0.41/0.59         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 0.41/0.59          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.41/0.59  thf('34', plain,
% 0.41/0.59      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.41/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.41/0.59  thf('35', plain,
% 0.41/0.59      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.41/0.59      inference('sup+', [status(thm)], ['12', '15'])).
% 0.41/0.59  thf('36', plain,
% 0.41/0.59      (((k3_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.41/0.59      inference('sup+', [status(thm)], ['34', '35'])).
% 0.41/0.59  thf('37', plain,
% 0.41/0.59      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.41/0.59         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.41/0.59      inference('split', [status(esa)], ['0'])).
% 0.41/0.59  thf('38', plain,
% 0.41/0.59      ((~ (r1_tarski @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C)))
% 0.41/0.59         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.41/0.59  thf('39', plain,
% 0.41/0.59      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.41/0.59       ~ ((r1_xboole_0 @ sk_B @ sk_C))),
% 0.41/0.59      inference('sup-', [status(thm)], ['31', '38'])).
% 0.41/0.59  thf('40', plain,
% 0.41/0.59      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.41/0.59       ((r1_xboole_0 @ sk_B @ sk_C))),
% 0.41/0.59      inference('split', [status(esa)], ['26'])).
% 0.41/0.59  thf('41', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.41/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.41/0.59  thf('42', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.59  thf(l97_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.41/0.59  thf('43', plain,
% 0.41/0.59      (![X2 : $i, X3 : $i]:
% 0.41/0.59         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ (k5_xboole_0 @ X2 @ X3))),
% 0.41/0.59      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.41/0.59  thf('44', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('sup+', [status(thm)], ['42', '43'])).
% 0.41/0.59  thf(t83_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.59  thf('45', plain,
% 0.41/0.59      (![X8 : $i, X9 : $i]:
% 0.41/0.59         (((k4_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.41/0.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.41/0.59  thf('46', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0))
% 0.41/0.59           = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.41/0.59  thf('47', plain,
% 0.41/0.59      (((k4_xboole_0 @ sk_C @ (k5_xboole_0 @ sk_A @ sk_C))
% 0.41/0.59         = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.41/0.59      inference('sup+', [status(thm)], ['41', '46'])).
% 0.41/0.59  thf('48', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.41/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.41/0.59  thf('49', plain,
% 0.41/0.59      (((k4_xboole_0 @ sk_C @ (k5_xboole_0 @ sk_A @ sk_C)) = (sk_C))),
% 0.41/0.59      inference('demod', [status(thm)], ['47', '48'])).
% 0.41/0.59  thf('50', plain,
% 0.41/0.59      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))
% 0.41/0.59         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.41/0.59      inference('split', [status(esa)], ['26'])).
% 0.41/0.59  thf(t85_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.41/0.59  thf('51', plain,
% 0.41/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.41/0.59         (~ (r1_tarski @ X11 @ X12)
% 0.41/0.59          | (r1_xboole_0 @ X11 @ (k4_xboole_0 @ X13 @ X12)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.41/0.59  thf('52', plain,
% 0.41/0.59      ((![X0 : $i]:
% 0.41/0.59          (r1_xboole_0 @ sk_B @ 
% 0.41/0.59           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C))))
% 0.41/0.59         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.41/0.59  thf('53', plain,
% 0.41/0.59      (![X8 : $i, X9 : $i]:
% 0.41/0.59         (((k4_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.41/0.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.41/0.59  thf('54', plain,
% 0.41/0.59      ((![X0 : $i]:
% 0.41/0.59          ((k4_xboole_0 @ sk_B @ 
% 0.41/0.59            (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C))) = (sk_B)))
% 0.41/0.59         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['52', '53'])).
% 0.41/0.59  thf('55', plain,
% 0.41/0.59      (((k3_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.41/0.59      inference('sup+', [status(thm)], ['34', '35'])).
% 0.41/0.59  thf('56', plain,
% 0.41/0.59      ((![X0 : $i]:
% 0.41/0.59          ((k4_xboole_0 @ sk_B @ 
% 0.41/0.59            (k4_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C))) = (sk_B)))
% 0.41/0.59         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.41/0.59      inference('demod', [status(thm)], ['54', '55'])).
% 0.41/0.59  thf('57', plain,
% 0.41/0.59      ((((k4_xboole_0 @ sk_B @ sk_C) = (sk_B)))
% 0.41/0.59         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.41/0.59      inference('sup+', [status(thm)], ['49', '56'])).
% 0.41/0.59  thf('58', plain,
% 0.41/0.59      (![X8 : $i, X10 : $i]:
% 0.41/0.59         ((r1_xboole_0 @ X8 @ X10) | ((k4_xboole_0 @ X8 @ X10) != (X8)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.41/0.59  thf('59', plain,
% 0.41/0.59      (((((sk_B) != (sk_B)) | (r1_xboole_0 @ sk_B @ sk_C)))
% 0.41/0.59         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['57', '58'])).
% 0.41/0.59  thf('60', plain,
% 0.41/0.59      (((r1_xboole_0 @ sk_B @ sk_C))
% 0.41/0.59         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.41/0.59      inference('simplify', [status(thm)], ['59'])).
% 0.41/0.59  thf('61', plain,
% 0.41/0.59      ((~ (r1_xboole_0 @ sk_B @ sk_C)) <= (~ ((r1_xboole_0 @ sk_B @ sk_C)))),
% 0.41/0.59      inference('split', [status(esa)], ['0'])).
% 0.41/0.59  thf('62', plain,
% 0.41/0.59      (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))) | 
% 0.41/0.59       ((r1_xboole_0 @ sk_B @ sk_C))),
% 0.41/0.59      inference('sup-', [status(thm)], ['60', '61'])).
% 0.41/0.59  thf('63', plain, ($false),
% 0.41/0.59      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '62'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
