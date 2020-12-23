%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6HoAjVRj4K

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:09 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 354 expanded)
%              Number of leaves         :   26 ( 115 expanded)
%              Depth                    :   16
%              Number of atoms          :  854 (3144 expanded)
%              Number of equality atoms :   45 ( 155 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t31_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ C )
            <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('6',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X28: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('14',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( r1_tarski @ X21 @ X19 )
      | ( X20
       != ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('16',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_tarski @ X21 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['14','16'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['8','9','19'])).

thf('21',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['20','27'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','30'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('35',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X28: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('40',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_tarski @ X21 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('42',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('44',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['35','46'])).

thf('48',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('49',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('51',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('54',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','56'])).

thf('58',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('59',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('60',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('61',plain,
    ( ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,
    ( ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      = ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('65',plain,
    ( ( ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      = ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('67',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('70',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('71',plain,
    ( ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('73',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('77',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) ) @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['20','27'])).

thf('81',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('83',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','57','58','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6HoAjVRj4K
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:54:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.77/0.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.77/0.99  % Solved by: fo/fo7.sh
% 0.77/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.99  % done 1790 iterations in 0.525s
% 0.77/0.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.77/0.99  % SZS output start Refutation
% 0.77/0.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.77/0.99  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.77/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.77/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.99  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.77/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/0.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/0.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.77/0.99  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.77/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.99  thf(t31_subset_1, conjecture,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.99       ( ![C:$i]:
% 0.77/0.99         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.99           ( ( r1_tarski @ B @ C ) <=>
% 0.77/0.99             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.77/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.99    (~( ![A:$i,B:$i]:
% 0.77/0.99        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.99          ( ![C:$i]:
% 0.77/0.99            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.99              ( ( r1_tarski @ B @ C ) <=>
% 0.77/0.99                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.77/0.99    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.77/0.99  thf('0', plain,
% 0.77/0.99      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99           (k3_subset_1 @ sk_A @ sk_B))
% 0.77/0.99        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('1', plain,
% 0.77/0.99      (~
% 0.77/0.99       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.77/0.99       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.77/0.99      inference('split', [status(esa)], ['0'])).
% 0.77/0.99  thf('2', plain,
% 0.77/0.99      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99         (k3_subset_1 @ sk_A @ sk_B))
% 0.77/0.99        | (r1_tarski @ sk_B @ sk_C_1))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('3', plain,
% 0.77/0.99      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.77/0.99      inference('split', [status(esa)], ['2'])).
% 0.77/0.99  thf('4', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf(d5_subset_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.99       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.77/0.99  thf('5', plain,
% 0.77/0.99      (![X26 : $i, X27 : $i]:
% 0.77/0.99         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 0.77/0.99          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.77/0.99      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.77/0.99  thf('6', plain,
% 0.77/0.99      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.77/0.99      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/0.99  thf(t48_xboole_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.77/0.99  thf('7', plain,
% 0.77/0.99      (![X16 : $i, X17 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.77/0.99           = (k3_xboole_0 @ X16 @ X17))),
% 0.77/0.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.99  thf('8', plain,
% 0.77/0.99      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.77/0.99         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.77/0.99      inference('sup+', [status(thm)], ['6', '7'])).
% 0.77/0.99  thf(commutativity_k3_xboole_0, axiom,
% 0.77/0.99    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.77/0.99  thf('9', plain,
% 0.77/0.99      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.99  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf(d2_subset_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( ( v1_xboole_0 @ A ) =>
% 0.77/0.99         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.77/0.99       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.77/0.99         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.77/0.99  thf('11', plain,
% 0.77/0.99      (![X23 : $i, X24 : $i]:
% 0.77/0.99         (~ (m1_subset_1 @ X23 @ X24)
% 0.77/0.99          | (r2_hidden @ X23 @ X24)
% 0.77/0.99          | (v1_xboole_0 @ X24))),
% 0.77/0.99      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.77/0.99  thf('12', plain,
% 0.77/0.99      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.77/0.99        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['10', '11'])).
% 0.77/0.99  thf(fc1_subset_1, axiom,
% 0.77/0.99    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.77/0.99  thf('13', plain, (![X28 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 0.77/0.99      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.77/0.99  thf('14', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.77/0.99      inference('clc', [status(thm)], ['12', '13'])).
% 0.77/0.99  thf(d1_zfmisc_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.77/0.99       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.77/0.99  thf('15', plain,
% 0.77/0.99      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.77/0.99         (~ (r2_hidden @ X21 @ X20)
% 0.77/0.99          | (r1_tarski @ X21 @ X19)
% 0.77/0.99          | ((X20) != (k1_zfmisc_1 @ X19)))),
% 0.77/0.99      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.77/0.99  thf('16', plain,
% 0.77/0.99      (![X19 : $i, X21 : $i]:
% 0.77/0.99         ((r1_tarski @ X21 @ X19) | ~ (r2_hidden @ X21 @ (k1_zfmisc_1 @ X19)))),
% 0.77/0.99      inference('simplify', [status(thm)], ['15'])).
% 0.77/0.99  thf('17', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.77/0.99      inference('sup-', [status(thm)], ['14', '16'])).
% 0.77/0.99  thf(t28_xboole_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.77/0.99  thf('18', plain,
% 0.77/0.99      (![X6 : $i, X7 : $i]:
% 0.77/0.99         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.77/0.99      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.77/0.99  thf('19', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.77/0.99      inference('sup-', [status(thm)], ['17', '18'])).
% 0.77/0.99  thf('20', plain,
% 0.77/0.99      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.77/0.99      inference('demod', [status(thm)], ['8', '9', '19'])).
% 0.77/0.99  thf('21', plain,
% 0.77/0.99      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.77/0.99      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/0.99  thf('22', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.77/0.99      inference('sup-', [status(thm)], ['17', '18'])).
% 0.77/0.99  thf('23', plain,
% 0.77/0.99      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.99  thf(t100_xboole_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.77/0.99  thf('24', plain,
% 0.77/0.99      (![X4 : $i, X5 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ X4 @ X5)
% 0.77/0.99           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.77/0.99      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.77/0.99  thf('25', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ X0 @ X1)
% 0.77/0.99           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['23', '24'])).
% 0.77/0.99  thf('26', plain,
% 0.77/0.99      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.77/0.99      inference('sup+', [status(thm)], ['22', '25'])).
% 0.77/0.99  thf('27', plain,
% 0.77/0.99      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.77/0.99      inference('sup+', [status(thm)], ['21', '26'])).
% 0.77/0.99  thf('28', plain,
% 0.77/0.99      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.77/0.99      inference('demod', [status(thm)], ['20', '27'])).
% 0.77/0.99  thf(t44_xboole_1, axiom,
% 0.77/0.99    (![A:$i,B:$i,C:$i]:
% 0.77/0.99     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.77/0.99       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.77/0.99  thf('29', plain,
% 0.77/0.99      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.77/0.99         ((r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 0.77/0.99          | ~ (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15))),
% 0.77/0.99      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.77/0.99  thf('30', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         (~ (r1_tarski @ sk_B @ X0)
% 0.77/0.99          | (r1_tarski @ sk_A @ 
% 0.77/0.99             (k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ X0)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['28', '29'])).
% 0.77/0.99  thf('31', plain,
% 0.77/0.99      (((r1_tarski @ sk_A @ 
% 0.77/0.99         (k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_C_1)))
% 0.77/0.99         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['3', '30'])).
% 0.77/0.99  thf(commutativity_k2_xboole_0, axiom,
% 0.77/0.99    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.77/0.99  thf('32', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.99  thf('33', plain,
% 0.77/0.99      (((r1_tarski @ sk_A @ 
% 0.77/0.99         (k2_xboole_0 @ sk_C_1 @ (k5_xboole_0 @ sk_A @ sk_B))))
% 0.77/0.99         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.77/0.99      inference('demod', [status(thm)], ['31', '32'])).
% 0.77/0.99  thf(t43_xboole_1, axiom,
% 0.77/0.99    (![A:$i,B:$i,C:$i]:
% 0.77/0.99     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.77/0.99       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.77/0.99  thf('34', plain,
% 0.77/0.99      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.77/0.99         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.77/0.99          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.77/0.99      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.77/0.99  thf('35', plain,
% 0.77/0.99      (((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.77/0.99         (k5_xboole_0 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['33', '34'])).
% 0.77/0.99  thf('36', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('37', plain,
% 0.77/0.99      (![X23 : $i, X24 : $i]:
% 0.77/0.99         (~ (m1_subset_1 @ X23 @ X24)
% 0.77/0.99          | (r2_hidden @ X23 @ X24)
% 0.77/0.99          | (v1_xboole_0 @ X24))),
% 0.77/0.99      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.77/0.99  thf('38', plain,
% 0.77/0.99      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.77/0.99        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['36', '37'])).
% 0.77/0.99  thf('39', plain, (![X28 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 0.77/0.99      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.77/0.99  thf('40', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.77/0.99      inference('clc', [status(thm)], ['38', '39'])).
% 0.77/0.99  thf('41', plain,
% 0.77/0.99      (![X19 : $i, X21 : $i]:
% 0.77/0.99         ((r1_tarski @ X21 @ X19) | ~ (r2_hidden @ X21 @ (k1_zfmisc_1 @ X19)))),
% 0.77/0.99      inference('simplify', [status(thm)], ['15'])).
% 0.77/0.99  thf('42', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.77/0.99      inference('sup-', [status(thm)], ['40', '41'])).
% 0.77/0.99  thf('43', plain,
% 0.77/0.99      (![X6 : $i, X7 : $i]:
% 0.77/0.99         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.77/0.99      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.77/0.99  thf('44', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.77/0.99      inference('sup-', [status(thm)], ['42', '43'])).
% 0.77/0.99  thf('45', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ X0 @ X1)
% 0.77/0.99           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.77/0.99      inference('sup+', [status(thm)], ['23', '24'])).
% 0.77/0.99  thf('46', plain,
% 0.77/0.99      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.77/0.99      inference('sup+', [status(thm)], ['44', '45'])).
% 0.77/0.99  thf('47', plain,
% 0.77/0.99      (((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.77/0.99         (k5_xboole_0 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.77/0.99      inference('demod', [status(thm)], ['35', '46'])).
% 0.77/0.99  thf('48', plain,
% 0.77/0.99      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.77/0.99      inference('sup+', [status(thm)], ['44', '45'])).
% 0.77/0.99  thf('49', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('50', plain,
% 0.77/0.99      (![X26 : $i, X27 : $i]:
% 0.77/0.99         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 0.77/0.99          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.77/0.99      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.77/0.99  thf('51', plain,
% 0.77/0.99      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.77/0.99      inference('sup-', [status(thm)], ['49', '50'])).
% 0.77/0.99  thf('52', plain,
% 0.77/0.99      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.77/0.99      inference('sup+', [status(thm)], ['48', '51'])).
% 0.77/0.99  thf('53', plain,
% 0.77/0.99      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.77/0.99      inference('sup+', [status(thm)], ['21', '26'])).
% 0.77/0.99  thf('54', plain,
% 0.77/0.99      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99           (k3_subset_1 @ sk_A @ sk_B)))
% 0.77/0.99         <= (~
% 0.77/0.99             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.77/0.99      inference('split', [status(esa)], ['0'])).
% 0.77/0.99  thf('55', plain,
% 0.77/0.99      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99           (k5_xboole_0 @ sk_A @ sk_B)))
% 0.77/0.99         <= (~
% 0.77/0.99             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.77/0.99      inference('sup-', [status(thm)], ['53', '54'])).
% 0.77/0.99  thf('56', plain,
% 0.77/0.99      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.77/0.99           (k5_xboole_0 @ sk_A @ sk_B)))
% 0.77/0.99         <= (~
% 0.77/0.99             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.77/0.99      inference('sup-', [status(thm)], ['52', '55'])).
% 0.77/0.99  thf('57', plain,
% 0.77/0.99      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.77/0.99       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.77/0.99      inference('sup-', [status(thm)], ['47', '56'])).
% 0.77/0.99  thf('58', plain,
% 0.77/0.99      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.77/0.99       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.77/0.99      inference('split', [status(esa)], ['2'])).
% 0.77/0.99  thf('59', plain,
% 0.77/0.99      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99         (k3_subset_1 @ sk_A @ sk_B)))
% 0.77/0.99         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.77/0.99      inference('split', [status(esa)], ['2'])).
% 0.77/0.99  thf('60', plain,
% 0.77/0.99      (![X6 : $i, X7 : $i]:
% 0.77/0.99         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.77/0.99      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.77/0.99  thf('61', plain,
% 0.77/0.99      ((((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99          (k3_subset_1 @ sk_A @ sk_B)) = (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.77/0.99         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.77/0.99      inference('sup-', [status(thm)], ['59', '60'])).
% 0.77/0.99  thf('62', plain,
% 0.77/0.99      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.99  thf('63', plain,
% 0.77/0.99      ((((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.77/0.99          (k3_subset_1 @ sk_A @ sk_C_1)) = (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.77/0.99         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.77/0.99      inference('demod', [status(thm)], ['61', '62'])).
% 0.77/0.99  thf('64', plain,
% 0.77/0.99      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.77/0.99      inference('sup+', [status(thm)], ['21', '26'])).
% 0.77/0.99  thf('65', plain,
% 0.77/0.99      ((((k3_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 0.77/0.99          (k3_subset_1 @ sk_A @ sk_C_1)) = (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.77/0.99         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.77/0.99      inference('demod', [status(thm)], ['63', '64'])).
% 0.77/0.99  thf('66', plain,
% 0.77/0.99      (![X16 : $i, X17 : $i]:
% 0.77/0.99         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.77/0.99           = (k3_xboole_0 @ X16 @ X17))),
% 0.77/0.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.99  thf(t36_xboole_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.77/0.99  thf('67', plain,
% 0.77/0.99      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.77/0.99      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.77/0.99  thf('68', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.77/0.99      inference('sup+', [status(thm)], ['66', '67'])).
% 0.77/0.99  thf('69', plain,
% 0.77/0.99      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99         (k5_xboole_0 @ sk_A @ sk_B)))
% 0.77/0.99         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.77/0.99      inference('sup+', [status(thm)], ['65', '68'])).
% 0.77/0.99  thf('70', plain,
% 0.77/0.99      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.77/0.99      inference('sup+', [status(thm)], ['48', '51'])).
% 0.77/0.99  thf('71', plain,
% 0.77/0.99      (((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.77/0.99         (k5_xboole_0 @ sk_A @ sk_B)))
% 0.77/0.99         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.77/0.99      inference('demod', [status(thm)], ['69', '70'])).
% 0.77/0.99  thf('72', plain,
% 0.77/0.99      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.77/0.99      inference('sup+', [status(thm)], ['44', '45'])).
% 0.77/0.99  thf('73', plain,
% 0.77/0.99      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.77/0.99         ((r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 0.77/0.99          | ~ (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15))),
% 0.77/0.99      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.77/0.99  thf('74', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ X0)
% 0.77/0.99          | (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['72', '73'])).
% 0.77/0.99  thf('75', plain,
% 0.77/0.99      (((r1_tarski @ sk_A @ 
% 0.77/0.99         (k2_xboole_0 @ sk_C_1 @ (k5_xboole_0 @ sk_A @ sk_B))))
% 0.77/0.99         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.77/0.99      inference('sup-', [status(thm)], ['71', '74'])).
% 0.77/0.99  thf('76', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.99  thf('77', plain,
% 0.77/0.99      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.77/0.99         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.77/0.99          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.77/0.99      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.77/0.99  thf('78', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.99         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.77/0.99          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 0.77/0.99      inference('sup-', [status(thm)], ['76', '77'])).
% 0.77/0.99  thf('79', plain,
% 0.77/0.99      (((r1_tarski @ (k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)) @ 
% 0.77/0.99         sk_C_1))
% 0.77/0.99         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.77/0.99      inference('sup-', [status(thm)], ['75', '78'])).
% 0.77/0.99  thf('80', plain,
% 0.77/0.99      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.77/0.99      inference('demod', [status(thm)], ['20', '27'])).
% 0.77/0.99  thf('81', plain,
% 0.77/0.99      (((r1_tarski @ sk_B @ sk_C_1))
% 0.77/0.99         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.77/0.99      inference('demod', [status(thm)], ['79', '80'])).
% 0.77/0.99  thf('82', plain,
% 0.77/0.99      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.77/0.99      inference('split', [status(esa)], ['0'])).
% 0.77/0.99  thf('83', plain,
% 0.77/0.99      (~
% 0.77/0.99       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.77/0.99         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.77/0.99       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.77/0.99      inference('sup-', [status(thm)], ['81', '82'])).
% 0.77/0.99  thf('84', plain, ($false),
% 0.77/0.99      inference('sat_resolution*', [status(thm)], ['1', '57', '58', '83'])).
% 0.77/0.99  
% 0.77/0.99  % SZS output end Refutation
% 0.77/0.99  
% 0.84/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
