%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.APe7fZSxwU

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:11 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 584 expanded)
%              Number of leaves         :   26 ( 184 expanded)
%              Depth                    :   20
%              Number of atoms          :  923 (5108 expanded)
%              Number of equality atoms :   42 ( 231 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X28: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('9',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( r1_tarski @ X19 @ X17 )
      | ( X18
       != ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('11',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_tarski @ X19 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['9','11'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('22',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X28: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('27',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_tarski @ X19 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('29',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','19','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['27','28'])).

thf('38',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_xboole_0 @ X10 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('47',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','18'])).

thf('49',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','33'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( r1_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['43','50'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('53',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('54',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X15 )
      | ( r1_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','55'])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('58',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','62'])).

thf('64',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['36','65'])).

thf('67',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['35','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('69',plain,(
    ! [X26: $i,X27: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('70',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('72',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('74',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X28: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('78',plain,(
    r2_hidden @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_tarski @ X19 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('80',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('82',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['44'])).

thf('83',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_xboole_0 @ X10 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('84',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('86',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_B )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X15 )
      | ( r1_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('88',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ ( k4_xboole_0 @ X1 @ sk_B ) )
        | ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ X1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ X0 )
        | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['81','88'])).

thf('90',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ X0 )
        | ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['44'])).

thf('93',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['36','65','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['91','93'])).

thf('95',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['80','94'])).

thf('96',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('97',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['67','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.APe7fZSxwU
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.57/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.57/0.77  % Solved by: fo/fo7.sh
% 0.57/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.77  % done 572 iterations in 0.290s
% 0.57/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.57/0.77  % SZS output start Refutation
% 0.57/0.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.57/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.77  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.57/0.77  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.57/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.57/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.57/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.57/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.57/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.57/0.77  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.57/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.77  thf(t31_subset_1, conjecture,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.57/0.77       ( ![C:$i]:
% 0.57/0.77         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.57/0.77           ( ( r1_tarski @ B @ C ) <=>
% 0.57/0.77             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.57/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.77    (~( ![A:$i,B:$i]:
% 0.57/0.77        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.57/0.77          ( ![C:$i]:
% 0.57/0.77            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.57/0.77              ( ( r1_tarski @ B @ C ) <=>
% 0.57/0.77                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.57/0.77    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.57/0.77  thf('0', plain,
% 0.57/0.77      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.57/0.77           (k3_subset_1 @ sk_A @ sk_B))
% 0.57/0.77        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('1', plain,
% 0.57/0.77      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.57/0.77           (k3_subset_1 @ sk_A @ sk_B)))
% 0.57/0.77         <= (~
% 0.57/0.77             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.57/0.77               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.57/0.77      inference('split', [status(esa)], ['0'])).
% 0.57/0.77  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf(d5_subset_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.57/0.77       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.57/0.77  thf('3', plain,
% 0.57/0.77      (![X24 : $i, X25 : $i]:
% 0.57/0.77         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 0.57/0.77          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.57/0.77      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.57/0.77  thf('4', plain,
% 0.57/0.77      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.57/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.57/0.77  thf('5', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf(d2_subset_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( ( v1_xboole_0 @ A ) =>
% 0.57/0.77         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.57/0.77       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.57/0.77         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.57/0.77  thf('6', plain,
% 0.57/0.77      (![X21 : $i, X22 : $i]:
% 0.57/0.77         (~ (m1_subset_1 @ X21 @ X22)
% 0.57/0.77          | (r2_hidden @ X21 @ X22)
% 0.57/0.77          | (v1_xboole_0 @ X22))),
% 0.57/0.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.57/0.77  thf('7', plain,
% 0.57/0.77      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.57/0.77        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.57/0.77  thf(fc1_subset_1, axiom,
% 0.57/0.77    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.57/0.77  thf('8', plain, (![X28 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 0.57/0.77      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.57/0.77  thf('9', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.57/0.77      inference('clc', [status(thm)], ['7', '8'])).
% 0.57/0.77  thf(d1_zfmisc_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.57/0.77       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.57/0.77  thf('10', plain,
% 0.57/0.77      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.57/0.77         (~ (r2_hidden @ X19 @ X18)
% 0.57/0.77          | (r1_tarski @ X19 @ X17)
% 0.57/0.77          | ((X18) != (k1_zfmisc_1 @ X17)))),
% 0.57/0.77      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.57/0.77  thf('11', plain,
% 0.57/0.77      (![X17 : $i, X19 : $i]:
% 0.57/0.77         ((r1_tarski @ X19 @ X17) | ~ (r2_hidden @ X19 @ (k1_zfmisc_1 @ X17)))),
% 0.57/0.77      inference('simplify', [status(thm)], ['10'])).
% 0.57/0.77  thf('12', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.57/0.77      inference('sup-', [status(thm)], ['9', '11'])).
% 0.57/0.77  thf(t28_xboole_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.57/0.77  thf('13', plain,
% 0.57/0.77      (![X6 : $i, X7 : $i]:
% 0.57/0.77         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.57/0.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.57/0.77  thf('14', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.57/0.77      inference('sup-', [status(thm)], ['12', '13'])).
% 0.57/0.77  thf(commutativity_k3_xboole_0, axiom,
% 0.57/0.77    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.57/0.77  thf('15', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.77  thf(t100_xboole_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.57/0.77  thf('16', plain,
% 0.57/0.77      (![X4 : $i, X5 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ X4 @ X5)
% 0.57/0.77           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.77  thf('17', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ X0 @ X1)
% 0.57/0.77           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['15', '16'])).
% 0.57/0.77  thf('18', plain,
% 0.57/0.77      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.57/0.77      inference('sup+', [status(thm)], ['14', '17'])).
% 0.57/0.77  thf('19', plain,
% 0.57/0.77      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.57/0.77      inference('demod', [status(thm)], ['4', '18'])).
% 0.57/0.77  thf('20', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('21', plain,
% 0.57/0.77      (![X24 : $i, X25 : $i]:
% 0.57/0.77         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 0.57/0.77          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.57/0.77      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.57/0.77  thf('22', plain,
% 0.57/0.77      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.57/0.77      inference('sup-', [status(thm)], ['20', '21'])).
% 0.57/0.77  thf('23', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('24', plain,
% 0.57/0.77      (![X21 : $i, X22 : $i]:
% 0.57/0.77         (~ (m1_subset_1 @ X21 @ X22)
% 0.57/0.77          | (r2_hidden @ X21 @ X22)
% 0.57/0.77          | (v1_xboole_0 @ X22))),
% 0.57/0.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.57/0.77  thf('25', plain,
% 0.57/0.77      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.57/0.77        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['23', '24'])).
% 0.57/0.77  thf('26', plain, (![X28 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 0.57/0.77      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.57/0.77  thf('27', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.57/0.77      inference('clc', [status(thm)], ['25', '26'])).
% 0.57/0.77  thf('28', plain,
% 0.57/0.77      (![X17 : $i, X19 : $i]:
% 0.57/0.77         ((r1_tarski @ X19 @ X17) | ~ (r2_hidden @ X19 @ (k1_zfmisc_1 @ X17)))),
% 0.57/0.77      inference('simplify', [status(thm)], ['10'])).
% 0.57/0.77  thf('29', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.57/0.77      inference('sup-', [status(thm)], ['27', '28'])).
% 0.57/0.77  thf('30', plain,
% 0.57/0.77      (![X6 : $i, X7 : $i]:
% 0.57/0.77         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.57/0.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.57/0.77  thf('31', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.57/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.57/0.77  thf('32', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ X0 @ X1)
% 0.57/0.77           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['15', '16'])).
% 0.57/0.77  thf('33', plain,
% 0.57/0.77      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.57/0.77      inference('sup+', [status(thm)], ['31', '32'])).
% 0.57/0.77  thf('34', plain,
% 0.57/0.77      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.57/0.77      inference('demod', [status(thm)], ['22', '33'])).
% 0.57/0.77  thf('35', plain,
% 0.57/0.77      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.57/0.77           (k5_xboole_0 @ sk_A @ sk_B)))
% 0.57/0.77         <= (~
% 0.57/0.77             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.57/0.77               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.57/0.77      inference('demod', [status(thm)], ['1', '19', '34'])).
% 0.57/0.77  thf('36', plain,
% 0.57/0.77      (~
% 0.57/0.77       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.57/0.77         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.57/0.77       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.57/0.77      inference('split', [status(esa)], ['0'])).
% 0.57/0.77  thf('37', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.57/0.77      inference('sup-', [status(thm)], ['27', '28'])).
% 0.57/0.77  thf('38', plain,
% 0.57/0.77      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.57/0.77      inference('sup+', [status(thm)], ['31', '32'])).
% 0.57/0.77  thf(t48_xboole_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.57/0.77  thf('39', plain,
% 0.57/0.77      (![X8 : $i, X9 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.57/0.77           = (k3_xboole_0 @ X8 @ X9))),
% 0.57/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.57/0.77  thf('40', plain,
% 0.57/0.77      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.57/0.77         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.57/0.77      inference('sup+', [status(thm)], ['38', '39'])).
% 0.57/0.77  thf('41', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.77  thf('42', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.57/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.57/0.77  thf('43', plain,
% 0.57/0.77      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.57/0.77      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.57/0.77  thf('44', plain,
% 0.57/0.77      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.57/0.77         (k3_subset_1 @ sk_A @ sk_B))
% 0.57/0.77        | (r1_tarski @ sk_B @ sk_C_1))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('45', plain,
% 0.57/0.77      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.57/0.77         (k3_subset_1 @ sk_A @ sk_B)))
% 0.57/0.77         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.57/0.77               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.57/0.77      inference('split', [status(esa)], ['44'])).
% 0.57/0.77  thf(t85_xboole_1, axiom,
% 0.57/0.77    (![A:$i,B:$i,C:$i]:
% 0.57/0.77     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.57/0.77  thf('46', plain,
% 0.57/0.77      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.57/0.77         (~ (r1_tarski @ X10 @ X11)
% 0.57/0.77          | (r1_xboole_0 @ X10 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.57/0.77  thf('47', plain,
% 0.57/0.77      ((![X0 : $i]:
% 0.57/0.77          (r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.57/0.77           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.57/0.77         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.57/0.77               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.57/0.77      inference('sup-', [status(thm)], ['45', '46'])).
% 0.57/0.77  thf('48', plain,
% 0.57/0.77      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.57/0.77      inference('demod', [status(thm)], ['4', '18'])).
% 0.57/0.77  thf('49', plain,
% 0.57/0.77      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.57/0.77      inference('demod', [status(thm)], ['22', '33'])).
% 0.57/0.77  thf('50', plain,
% 0.57/0.77      ((![X0 : $i]:
% 0.57/0.77          (r1_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.57/0.77           (k4_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_B))))
% 0.57/0.77         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.57/0.77               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.57/0.77      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.57/0.77  thf('51', plain,
% 0.57/0.77      (((r1_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_B))
% 0.57/0.77         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.57/0.77               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.57/0.77      inference('sup+', [status(thm)], ['43', '50'])).
% 0.57/0.77  thf(symmetry_r1_xboole_0, axiom,
% 0.57/0.77    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.57/0.77  thf('52', plain,
% 0.57/0.77      (![X2 : $i, X3 : $i]:
% 0.57/0.77         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.57/0.77      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.57/0.77  thf('53', plain,
% 0.57/0.77      (((r1_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1)))
% 0.57/0.77         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.57/0.77               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.57/0.77      inference('sup-', [status(thm)], ['51', '52'])).
% 0.57/0.77  thf(t86_xboole_1, axiom,
% 0.57/0.77    (![A:$i,B:$i,C:$i]:
% 0.57/0.77     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.57/0.77       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.57/0.77  thf('54', plain,
% 0.57/0.77      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.57/0.77         (~ (r1_tarski @ X13 @ X14)
% 0.57/0.77          | ~ (r1_xboole_0 @ X13 @ X15)
% 0.57/0.77          | (r1_tarski @ X13 @ (k4_xboole_0 @ X14 @ X15)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.57/0.77  thf('55', plain,
% 0.57/0.77      ((![X0 : $i]:
% 0.57/0.77          ((r1_tarski @ sk_B @ 
% 0.57/0.77            (k4_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_1)))
% 0.57/0.77           | ~ (r1_tarski @ sk_B @ X0)))
% 0.57/0.77         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.57/0.77               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.57/0.77      inference('sup-', [status(thm)], ['53', '54'])).
% 0.57/0.77  thf('56', plain,
% 0.57/0.77      (((r1_tarski @ sk_B @ 
% 0.57/0.77         (k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1))))
% 0.57/0.77         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.57/0.77               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.57/0.77      inference('sup-', [status(thm)], ['37', '55'])).
% 0.57/0.77  thf('57', plain,
% 0.57/0.77      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.57/0.77      inference('sup+', [status(thm)], ['14', '17'])).
% 0.57/0.77  thf('58', plain,
% 0.57/0.77      (![X8 : $i, X9 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.57/0.77           = (k3_xboole_0 @ X8 @ X9))),
% 0.57/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.57/0.77  thf('59', plain,
% 0.57/0.77      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 0.57/0.77         = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.57/0.77      inference('sup+', [status(thm)], ['57', '58'])).
% 0.57/0.77  thf('60', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.77  thf('61', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.57/0.77      inference('sup-', [status(thm)], ['12', '13'])).
% 0.57/0.77  thf('62', plain,
% 0.57/0.77      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1)) = (sk_C_1))),
% 0.57/0.77      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.57/0.77  thf('63', plain,
% 0.57/0.77      (((r1_tarski @ sk_B @ sk_C_1))
% 0.57/0.77         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.57/0.77               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.57/0.77      inference('demod', [status(thm)], ['56', '62'])).
% 0.57/0.77  thf('64', plain,
% 0.57/0.77      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.57/0.77      inference('split', [status(esa)], ['0'])).
% 0.57/0.77  thf('65', plain,
% 0.57/0.77      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.57/0.77       ~
% 0.57/0.77       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.57/0.77         (k3_subset_1 @ sk_A @ sk_B)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['63', '64'])).
% 0.57/0.77  thf('66', plain,
% 0.57/0.77      (~
% 0.57/0.77       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.57/0.77         (k3_subset_1 @ sk_A @ sk_B)))),
% 0.57/0.77      inference('sat_resolution*', [status(thm)], ['36', '65'])).
% 0.57/0.77  thf('67', plain,
% 0.57/0.77      (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.57/0.77          (k5_xboole_0 @ sk_A @ sk_B))),
% 0.57/0.77      inference('simpl_trail', [status(thm)], ['35', '66'])).
% 0.57/0.77  thf('68', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf(dt_k3_subset_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.57/0.77       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.57/0.77  thf('69', plain,
% 0.57/0.77      (![X26 : $i, X27 : $i]:
% 0.57/0.77         ((m1_subset_1 @ (k3_subset_1 @ X26 @ X27) @ (k1_zfmisc_1 @ X26))
% 0.57/0.77          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.57/0.77      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.57/0.77  thf('70', plain,
% 0.57/0.77      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.57/0.77      inference('sup-', [status(thm)], ['68', '69'])).
% 0.57/0.77  thf('71', plain,
% 0.57/0.77      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.57/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.57/0.77  thf('72', plain,
% 0.57/0.77      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.57/0.77      inference('demod', [status(thm)], ['70', '71'])).
% 0.57/0.77  thf('73', plain,
% 0.57/0.77      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.57/0.77      inference('sup+', [status(thm)], ['14', '17'])).
% 0.57/0.77  thf('74', plain,
% 0.57/0.77      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.57/0.77      inference('demod', [status(thm)], ['72', '73'])).
% 0.57/0.77  thf('75', plain,
% 0.57/0.77      (![X21 : $i, X22 : $i]:
% 0.57/0.77         (~ (m1_subset_1 @ X21 @ X22)
% 0.57/0.77          | (r2_hidden @ X21 @ X22)
% 0.57/0.77          | (v1_xboole_0 @ X22))),
% 0.57/0.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.57/0.77  thf('76', plain,
% 0.57/0.77      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.57/0.77        | (r2_hidden @ (k5_xboole_0 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['74', '75'])).
% 0.57/0.77  thf('77', plain, (![X28 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 0.57/0.77      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.57/0.77  thf('78', plain,
% 0.57/0.77      ((r2_hidden @ (k5_xboole_0 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.57/0.77      inference('clc', [status(thm)], ['76', '77'])).
% 0.57/0.77  thf('79', plain,
% 0.57/0.77      (![X17 : $i, X19 : $i]:
% 0.57/0.77         ((r1_tarski @ X19 @ X17) | ~ (r2_hidden @ X19 @ (k1_zfmisc_1 @ X17)))),
% 0.57/0.77      inference('simplify', [status(thm)], ['10'])).
% 0.57/0.77  thf('80', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_A)),
% 0.57/0.77      inference('sup-', [status(thm)], ['78', '79'])).
% 0.57/0.77  thf('81', plain,
% 0.57/0.77      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.57/0.77      inference('sup+', [status(thm)], ['14', '17'])).
% 0.57/0.77  thf('82', plain,
% 0.57/0.77      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.57/0.77      inference('split', [status(esa)], ['44'])).
% 0.57/0.77  thf('83', plain,
% 0.57/0.77      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.57/0.77         (~ (r1_tarski @ X10 @ X11)
% 0.57/0.77          | (r1_xboole_0 @ X10 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.57/0.77  thf('84', plain,
% 0.57/0.77      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1)))
% 0.57/0.77         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['82', '83'])).
% 0.57/0.77  thf('85', plain,
% 0.57/0.77      (![X2 : $i, X3 : $i]:
% 0.57/0.77         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.57/0.77      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.57/0.77  thf('86', plain,
% 0.57/0.77      ((![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_B))
% 0.57/0.77         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['84', '85'])).
% 0.57/0.77  thf('87', plain,
% 0.57/0.77      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.57/0.77         (~ (r1_tarski @ X13 @ X14)
% 0.57/0.77          | ~ (r1_xboole_0 @ X13 @ X15)
% 0.57/0.77          | (r1_tarski @ X13 @ (k4_xboole_0 @ X14 @ X15)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.57/0.77  thf('88', plain,
% 0.57/0.77      ((![X0 : $i, X1 : $i]:
% 0.57/0.77          ((r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ (k4_xboole_0 @ X1 @ sk_B))
% 0.57/0.77           | ~ (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ X1)))
% 0.57/0.77         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['86', '87'])).
% 0.57/0.77  thf('89', plain,
% 0.57/0.77      ((![X0 : $i]:
% 0.57/0.77          (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ X0)
% 0.57/0.77           | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.57/0.77              (k4_xboole_0 @ X0 @ sk_B))))
% 0.57/0.77         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['81', '88'])).
% 0.57/0.77  thf('90', plain,
% 0.57/0.77      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.57/0.77      inference('sup+', [status(thm)], ['14', '17'])).
% 0.57/0.77  thf('91', plain,
% 0.57/0.77      ((![X0 : $i]:
% 0.57/0.77          (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ X0)
% 0.57/0.77           | (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.57/0.77              (k4_xboole_0 @ X0 @ sk_B))))
% 0.57/0.77         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.57/0.77      inference('demod', [status(thm)], ['89', '90'])).
% 0.57/0.77  thf('92', plain,
% 0.57/0.77      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.57/0.77       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.57/0.77         (k3_subset_1 @ sk_A @ sk_B)))),
% 0.57/0.77      inference('split', [status(esa)], ['44'])).
% 0.57/0.77  thf('93', plain, (((r1_tarski @ sk_B @ sk_C_1))),
% 0.57/0.77      inference('sat_resolution*', [status(thm)], ['36', '65', '92'])).
% 0.57/0.77  thf('94', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ X0)
% 0.57/0.77          | (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.57/0.77             (k4_xboole_0 @ X0 @ sk_B)))),
% 0.57/0.77      inference('simpl_trail', [status(thm)], ['91', '93'])).
% 0.57/0.77  thf('95', plain,
% 0.57/0.77      ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.57/0.77      inference('sup-', [status(thm)], ['80', '94'])).
% 0.57/0.77  thf('96', plain,
% 0.57/0.77      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.57/0.77      inference('sup+', [status(thm)], ['31', '32'])).
% 0.57/0.77  thf('97', plain,
% 0.57/0.77      ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ (k5_xboole_0 @ sk_A @ sk_B))),
% 0.57/0.77      inference('demod', [status(thm)], ['95', '96'])).
% 0.57/0.77  thf('98', plain, ($false), inference('demod', [status(thm)], ['67', '97'])).
% 0.57/0.77  
% 0.57/0.77  % SZS output end Refutation
% 0.57/0.77  
% 0.57/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
