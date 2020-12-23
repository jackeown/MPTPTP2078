%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6K0pz59MQ0

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:08 EST 2020

% Result     : Theorem 2.67s
% Output     : Refutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 568 expanded)
%              Number of leaves         :   31 ( 181 expanded)
%              Depth                    :   17
%              Number of atoms          : 1200 (4672 expanded)
%              Number of equality atoms :   63 ( 261 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf('2',plain,(
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

thf('3',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ X35 )
      | ( r2_hidden @ X34 @ X35 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X39: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('6',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X32 @ X31 )
      | ( r1_tarski @ X32 @ X30 )
      | ( X31
       != ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('8',plain,(
    ! [X30: $i,X32: $i] :
      ( ( r1_tarski @ X32 @ X30 )
      | ~ ( r2_hidden @ X32 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['16'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ( r1_tarski @ ( k4_xboole_0 @ X23 @ X22 ) @ ( k4_xboole_0 @ X23 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['15','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ X35 )
      | ( r2_hidden @ X34 @ X35 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X39: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('25',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X30: $i,X32: $i] :
      ( ( r1_tarski @ X32 @ X30 )
      | ~ ( r2_hidden @ X32 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('27',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['20','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X37 @ X38 )
        = ( k4_xboole_0 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('36',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X37 @ X38 )
        = ( k4_xboole_0 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('41',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','45'])).

thf('47',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['16'])).

thf('48',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['49'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('51',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('53',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['48','56'])).

thf('58',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('60',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X14 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['57','66'])).

thf('68',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['48','56'])).

thf('69',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('71',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('72',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X11 @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('74',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('78',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['6','8'])).

thf('79',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('80',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X14 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C_1 @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('84',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('86',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r1_tarski @ X26 @ X27 )
      | ~ ( r1_tarski @ X26 @ ( k2_xboole_0 @ X27 @ X28 ) )
      | ~ ( r1_xboole_0 @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X2 @ X1 )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( r1_tarski @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,(
    r1_tarski @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['76','89'])).

thf('91',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('92',plain,(
    r1_tarski @ sk_C_1 @ ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('94',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) @ sk_C_1 )
    | ( ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('96',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('97',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('99',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('102',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r1_tarski @ X26 @ X27 )
      | ~ ( r1_tarski @ X26 @ ( k2_xboole_0 @ X27 @ X28 ) )
      | ~ ( r1_xboole_0 @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) @ sk_C_1 ),
    inference('sup+',[status(thm)],['99','106'])).

thf('108',plain,
    ( ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['94','107'])).

thf('109',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['69','108'])).

thf('110',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('111',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('112',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('113',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X11 @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('117',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['110','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('120',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('121',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('122',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X14 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','127'])).

thf('129',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['109','128'])).

thf('130',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('131',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','46','47','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6K0pz59MQ0
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:13:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 2.67/2.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.67/2.90  % Solved by: fo/fo7.sh
% 2.67/2.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.67/2.90  % done 5798 iterations in 2.454s
% 2.67/2.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.67/2.90  % SZS output start Refutation
% 2.67/2.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.67/2.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.67/2.90  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.67/2.90  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.67/2.90  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.67/2.90  thf(sk_A_type, type, sk_A: $i).
% 2.67/2.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.67/2.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.67/2.90  thf(sk_B_type, type, sk_B: $i).
% 2.67/2.90  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.67/2.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.67/2.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.67/2.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.67/2.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.67/2.90  thf(t31_subset_1, conjecture,
% 2.67/2.90    (![A:$i,B:$i]:
% 2.67/2.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.67/2.90       ( ![C:$i]:
% 2.67/2.90         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.67/2.90           ( ( r1_tarski @ B @ C ) <=>
% 2.67/2.90             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 2.67/2.90  thf(zf_stmt_0, negated_conjecture,
% 2.67/2.90    (~( ![A:$i,B:$i]:
% 2.67/2.90        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.67/2.90          ( ![C:$i]:
% 2.67/2.90            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.67/2.90              ( ( r1_tarski @ B @ C ) <=>
% 2.67/2.90                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 2.67/2.90    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 2.67/2.90  thf('0', plain,
% 2.67/2.90      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.90           (k3_subset_1 @ sk_A @ sk_B))
% 2.67/2.90        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 2.67/2.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.90  thf('1', plain,
% 2.67/2.90      (~
% 2.67/2.90       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.90         (k3_subset_1 @ sk_A @ sk_B))) | 
% 2.67/2.90       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 2.67/2.90      inference('split', [status(esa)], ['0'])).
% 2.67/2.90  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.67/2.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.90  thf(d2_subset_1, axiom,
% 2.67/2.90    (![A:$i,B:$i]:
% 2.67/2.90     ( ( ( v1_xboole_0 @ A ) =>
% 2.67/2.90         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 2.67/2.90       ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.67/2.90         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 2.67/2.90  thf('3', plain,
% 2.67/2.90      (![X34 : $i, X35 : $i]:
% 2.67/2.90         (~ (m1_subset_1 @ X34 @ X35)
% 2.67/2.90          | (r2_hidden @ X34 @ X35)
% 2.67/2.90          | (v1_xboole_0 @ X35))),
% 2.67/2.90      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.67/2.90  thf('4', plain,
% 2.67/2.90      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 2.67/2.90        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 2.67/2.90      inference('sup-', [status(thm)], ['2', '3'])).
% 2.67/2.90  thf(fc1_subset_1, axiom,
% 2.67/2.90    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.67/2.90  thf('5', plain, (![X39 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X39))),
% 2.67/2.90      inference('cnf', [status(esa)], [fc1_subset_1])).
% 2.67/2.90  thf('6', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.67/2.90      inference('clc', [status(thm)], ['4', '5'])).
% 2.67/2.90  thf(d1_zfmisc_1, axiom,
% 2.67/2.90    (![A:$i,B:$i]:
% 2.67/2.90     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 2.67/2.90       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 2.67/2.90  thf('7', plain,
% 2.67/2.90      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.67/2.90         (~ (r2_hidden @ X32 @ X31)
% 2.67/2.90          | (r1_tarski @ X32 @ X30)
% 2.67/2.90          | ((X31) != (k1_zfmisc_1 @ X30)))),
% 2.67/2.90      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 2.67/2.90  thf('8', plain,
% 2.67/2.90      (![X30 : $i, X32 : $i]:
% 2.67/2.90         ((r1_tarski @ X32 @ X30) | ~ (r2_hidden @ X32 @ (k1_zfmisc_1 @ X30)))),
% 2.67/2.90      inference('simplify', [status(thm)], ['7'])).
% 2.67/2.90  thf('9', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 2.67/2.90      inference('sup-', [status(thm)], ['6', '8'])).
% 2.67/2.90  thf(t28_xboole_1, axiom,
% 2.67/2.90    (![A:$i,B:$i]:
% 2.67/2.90     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.67/2.90  thf('10', plain,
% 2.67/2.90      (![X19 : $i, X20 : $i]:
% 2.67/2.90         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 2.67/2.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.67/2.90  thf('11', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 2.67/2.90      inference('sup-', [status(thm)], ['9', '10'])).
% 2.67/2.90  thf(commutativity_k3_xboole_0, axiom,
% 2.67/2.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.67/2.90  thf('12', plain,
% 2.67/2.90      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.67/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.67/2.90  thf(t100_xboole_1, axiom,
% 2.67/2.90    (![A:$i,B:$i]:
% 2.67/2.90     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.67/2.90  thf('13', plain,
% 2.67/2.90      (![X9 : $i, X10 : $i]:
% 2.67/2.90         ((k4_xboole_0 @ X9 @ X10)
% 2.67/2.90           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 2.67/2.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.67/2.90  thf('14', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i]:
% 2.67/2.90         ((k4_xboole_0 @ X0 @ X1)
% 2.67/2.90           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.67/2.90      inference('sup+', [status(thm)], ['12', '13'])).
% 2.67/2.90  thf('15', plain,
% 2.67/2.90      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.67/2.90      inference('sup+', [status(thm)], ['11', '14'])).
% 2.67/2.90  thf('16', plain,
% 2.67/2.90      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.90         (k3_subset_1 @ sk_A @ sk_B))
% 2.67/2.90        | (r1_tarski @ sk_B @ sk_C_1))),
% 2.67/2.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.90  thf('17', plain,
% 2.67/2.90      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 2.67/2.90      inference('split', [status(esa)], ['16'])).
% 2.67/2.90  thf(t34_xboole_1, axiom,
% 2.67/2.90    (![A:$i,B:$i,C:$i]:
% 2.67/2.90     ( ( r1_tarski @ A @ B ) =>
% 2.67/2.90       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 2.67/2.90  thf('18', plain,
% 2.67/2.90      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.67/2.90         (~ (r1_tarski @ X21 @ X22)
% 2.67/2.90          | (r1_tarski @ (k4_xboole_0 @ X23 @ X22) @ (k4_xboole_0 @ X23 @ X21)))),
% 2.67/2.90      inference('cnf', [status(esa)], [t34_xboole_1])).
% 2.67/2.90  thf('19', plain,
% 2.67/2.90      ((![X0 : $i]:
% 2.67/2.90          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ (k4_xboole_0 @ X0 @ sk_B)))
% 2.67/2.90         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 2.67/2.90      inference('sup-', [status(thm)], ['17', '18'])).
% 2.67/2.90  thf('20', plain,
% 2.67/2.90      (((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 2.67/2.90         (k4_xboole_0 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 2.67/2.90      inference('sup+', [status(thm)], ['15', '19'])).
% 2.67/2.90  thf('21', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.67/2.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.90  thf('22', plain,
% 2.67/2.90      (![X34 : $i, X35 : $i]:
% 2.67/2.90         (~ (m1_subset_1 @ X34 @ X35)
% 2.67/2.90          | (r2_hidden @ X34 @ X35)
% 2.67/2.90          | (v1_xboole_0 @ X35))),
% 2.67/2.90      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.67/2.90  thf('23', plain,
% 2.67/2.90      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 2.67/2.90        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 2.67/2.90      inference('sup-', [status(thm)], ['21', '22'])).
% 2.67/2.90  thf('24', plain, (![X39 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X39))),
% 2.67/2.90      inference('cnf', [status(esa)], [fc1_subset_1])).
% 2.67/2.90  thf('25', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.67/2.90      inference('clc', [status(thm)], ['23', '24'])).
% 2.67/2.90  thf('26', plain,
% 2.67/2.90      (![X30 : $i, X32 : $i]:
% 2.67/2.90         ((r1_tarski @ X32 @ X30) | ~ (r2_hidden @ X32 @ (k1_zfmisc_1 @ X30)))),
% 2.67/2.90      inference('simplify', [status(thm)], ['7'])).
% 2.67/2.90  thf('27', plain, ((r1_tarski @ sk_B @ sk_A)),
% 2.67/2.90      inference('sup-', [status(thm)], ['25', '26'])).
% 2.67/2.90  thf('28', plain,
% 2.67/2.90      (![X19 : $i, X20 : $i]:
% 2.67/2.90         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 2.67/2.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.67/2.90  thf('29', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 2.67/2.90      inference('sup-', [status(thm)], ['27', '28'])).
% 2.67/2.90  thf('30', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i]:
% 2.67/2.90         ((k4_xboole_0 @ X0 @ X1)
% 2.67/2.90           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.67/2.90      inference('sup+', [status(thm)], ['12', '13'])).
% 2.67/2.90  thf('31', plain,
% 2.67/2.90      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 2.67/2.90      inference('sup+', [status(thm)], ['29', '30'])).
% 2.67/2.90  thf('32', plain,
% 2.67/2.90      (((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 2.67/2.90         (k5_xboole_0 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 2.67/2.90      inference('demod', [status(thm)], ['20', '31'])).
% 2.67/2.90  thf('33', plain,
% 2.67/2.90      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.67/2.90      inference('sup+', [status(thm)], ['11', '14'])).
% 2.67/2.90  thf('34', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.67/2.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.90  thf(d5_subset_1, axiom,
% 2.67/2.90    (![A:$i,B:$i]:
% 2.67/2.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.67/2.90       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.67/2.90  thf('35', plain,
% 2.67/2.90      (![X37 : $i, X38 : $i]:
% 2.67/2.90         (((k3_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))
% 2.67/2.90          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 2.67/2.90      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.67/2.90  thf('36', plain,
% 2.67/2.90      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 2.67/2.90      inference('sup-', [status(thm)], ['34', '35'])).
% 2.67/2.90  thf('37', plain,
% 2.67/2.90      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.67/2.90      inference('sup+', [status(thm)], ['33', '36'])).
% 2.67/2.90  thf('38', plain,
% 2.67/2.90      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 2.67/2.90      inference('sup+', [status(thm)], ['29', '30'])).
% 2.67/2.90  thf('39', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.67/2.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.90  thf('40', plain,
% 2.67/2.90      (![X37 : $i, X38 : $i]:
% 2.67/2.90         (((k3_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))
% 2.67/2.90          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 2.67/2.90      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.67/2.90  thf('41', plain,
% 2.67/2.90      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 2.67/2.90      inference('sup-', [status(thm)], ['39', '40'])).
% 2.67/2.90  thf('42', plain,
% 2.67/2.90      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 2.67/2.90      inference('sup+', [status(thm)], ['38', '41'])).
% 2.67/2.90  thf('43', plain,
% 2.67/2.90      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.90           (k3_subset_1 @ sk_A @ sk_B)))
% 2.67/2.90         <= (~
% 2.67/2.90             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.90               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.67/2.90      inference('split', [status(esa)], ['0'])).
% 2.67/2.90  thf('44', plain,
% 2.67/2.90      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.90           (k5_xboole_0 @ sk_A @ sk_B)))
% 2.67/2.90         <= (~
% 2.67/2.90             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.90               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.67/2.90      inference('sup-', [status(thm)], ['42', '43'])).
% 2.67/2.90  thf('45', plain,
% 2.67/2.90      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 2.67/2.90           (k5_xboole_0 @ sk_A @ sk_B)))
% 2.67/2.90         <= (~
% 2.67/2.90             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.90               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.67/2.90      inference('sup-', [status(thm)], ['37', '44'])).
% 2.67/2.90  thf('46', plain,
% 2.67/2.90      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.90         (k3_subset_1 @ sk_A @ sk_B))) | 
% 2.67/2.90       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 2.67/2.90      inference('sup-', [status(thm)], ['32', '45'])).
% 2.67/2.90  thf('47', plain,
% 2.67/2.90      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.90         (k3_subset_1 @ sk_A @ sk_B))) | 
% 2.67/2.90       ((r1_tarski @ sk_B @ sk_C_1))),
% 2.67/2.90      inference('split', [status(esa)], ['16'])).
% 2.67/2.90  thf('48', plain,
% 2.67/2.90      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.67/2.90      inference('sup+', [status(thm)], ['11', '14'])).
% 2.67/2.90  thf(d10_xboole_0, axiom,
% 2.67/2.90    (![A:$i,B:$i]:
% 2.67/2.90     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.67/2.90  thf('49', plain,
% 2.67/2.90      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 2.67/2.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.67/2.90  thf('50', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 2.67/2.90      inference('simplify', [status(thm)], ['49'])).
% 2.67/2.90  thf(t106_xboole_1, axiom,
% 2.67/2.90    (![A:$i,B:$i,C:$i]:
% 2.67/2.90     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 2.67/2.90       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 2.67/2.90  thf('51', plain,
% 2.67/2.90      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.67/2.90         ((r1_tarski @ X11 @ X12)
% 2.67/2.90          | ~ (r1_tarski @ X11 @ (k4_xboole_0 @ X12 @ X13)))),
% 2.67/2.90      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.67/2.90  thf('52', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 2.67/2.90      inference('sup-', [status(thm)], ['50', '51'])).
% 2.67/2.90  thf(t12_xboole_1, axiom,
% 2.67/2.90    (![A:$i,B:$i]:
% 2.67/2.90     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.67/2.90  thf('53', plain,
% 2.67/2.90      (![X17 : $i, X18 : $i]:
% 2.67/2.90         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 2.67/2.90      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.67/2.90  thf('54', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i]:
% 2.67/2.90         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 2.67/2.90      inference('sup-', [status(thm)], ['52', '53'])).
% 2.67/2.90  thf(commutativity_k2_xboole_0, axiom,
% 2.67/2.90    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.67/2.90  thf('55', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.67/2.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.67/2.90  thf('56', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i]:
% 2.67/2.90         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 2.67/2.90      inference('demod', [status(thm)], ['54', '55'])).
% 2.67/2.90  thf('57', plain,
% 2.67/2.90      (((k2_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1)) = (sk_A))),
% 2.67/2.90      inference('sup+', [status(thm)], ['48', '56'])).
% 2.67/2.90  thf('58', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 2.67/2.90      inference('simplify', [status(thm)], ['49'])).
% 2.67/2.90  thf('59', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.67/2.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.67/2.90  thf(t11_xboole_1, axiom,
% 2.67/2.90    (![A:$i,B:$i,C:$i]:
% 2.67/2.90     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 2.67/2.90  thf('60', plain,
% 2.67/2.90      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.67/2.90         ((r1_tarski @ X14 @ X15)
% 2.67/2.90          | ~ (r1_tarski @ (k2_xboole_0 @ X14 @ X16) @ X15))),
% 2.67/2.90      inference('cnf', [status(esa)], [t11_xboole_1])).
% 2.67/2.90  thf('61', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.90         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 2.67/2.90      inference('sup-', [status(thm)], ['59', '60'])).
% 2.67/2.90  thf('62', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.67/2.90      inference('sup-', [status(thm)], ['58', '61'])).
% 2.67/2.90  thf('63', plain,
% 2.67/2.90      (![X19 : $i, X20 : $i]:
% 2.67/2.90         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 2.67/2.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.67/2.90  thf('64', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i]:
% 2.67/2.90         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 2.67/2.90      inference('sup-', [status(thm)], ['62', '63'])).
% 2.67/2.90  thf('65', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i]:
% 2.67/2.90         ((k4_xboole_0 @ X0 @ X1)
% 2.67/2.90           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.67/2.90      inference('sup+', [status(thm)], ['12', '13'])).
% 2.67/2.90  thf('66', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i]:
% 2.67/2.90         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 2.67/2.90           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 2.67/2.90      inference('sup+', [status(thm)], ['64', '65'])).
% 2.67/2.90  thf('67', plain,
% 2.67/2.90      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 2.67/2.90         = (k5_xboole_0 @ 
% 2.67/2.90            (k2_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1)) @ 
% 2.67/2.90            (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 2.67/2.90      inference('sup+', [status(thm)], ['57', '66'])).
% 2.67/2.90  thf('68', plain,
% 2.67/2.90      (((k2_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1)) = (sk_A))),
% 2.67/2.90      inference('sup+', [status(thm)], ['48', '56'])).
% 2.67/2.90  thf('69', plain,
% 2.67/2.90      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 2.67/2.90         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 2.67/2.90      inference('demod', [status(thm)], ['67', '68'])).
% 2.67/2.90  thf('70', plain,
% 2.67/2.90      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.67/2.90      inference('sup+', [status(thm)], ['11', '14'])).
% 2.67/2.90  thf('71', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 2.67/2.90      inference('simplify', [status(thm)], ['49'])).
% 2.67/2.90  thf('72', plain,
% 2.67/2.90      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.67/2.90         ((r1_xboole_0 @ X11 @ X13)
% 2.67/2.90          | ~ (r1_tarski @ X11 @ (k4_xboole_0 @ X12 @ X13)))),
% 2.67/2.90      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.67/2.90  thf('73', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 2.67/2.90      inference('sup-', [status(thm)], ['71', '72'])).
% 2.67/2.90  thf(symmetry_r1_xboole_0, axiom,
% 2.67/2.90    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.67/2.90  thf('74', plain,
% 2.67/2.90      (![X4 : $i, X5 : $i]:
% 2.67/2.90         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 2.67/2.90      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.67/2.90  thf('75', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.67/2.90      inference('sup-', [status(thm)], ['73', '74'])).
% 2.67/2.90  thf('76', plain, ((r1_xboole_0 @ sk_C_1 @ (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.67/2.90      inference('sup+', [status(thm)], ['70', '75'])).
% 2.67/2.90  thf('77', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.67/2.90      inference('sup-', [status(thm)], ['58', '61'])).
% 2.67/2.90  thf('78', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 2.67/2.90      inference('sup-', [status(thm)], ['6', '8'])).
% 2.67/2.90  thf('79', plain,
% 2.67/2.90      (![X17 : $i, X18 : $i]:
% 2.67/2.90         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 2.67/2.90      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.67/2.90  thf('80', plain, (((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 2.67/2.90      inference('sup-', [status(thm)], ['78', '79'])).
% 2.67/2.90  thf('81', plain,
% 2.67/2.90      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.67/2.90         ((r1_tarski @ X14 @ X15)
% 2.67/2.90          | ~ (r1_tarski @ (k2_xboole_0 @ X14 @ X16) @ X15))),
% 2.67/2.90      inference('cnf', [status(esa)], [t11_xboole_1])).
% 2.67/2.90  thf('82', plain,
% 2.67/2.90      (![X0 : $i]: (~ (r1_tarski @ sk_A @ X0) | (r1_tarski @ sk_C_1 @ X0))),
% 2.67/2.90      inference('sup-', [status(thm)], ['80', '81'])).
% 2.67/2.90  thf('83', plain,
% 2.67/2.90      (![X0 : $i]: (r1_tarski @ sk_C_1 @ (k2_xboole_0 @ X0 @ sk_A))),
% 2.67/2.90      inference('sup-', [status(thm)], ['77', '82'])).
% 2.67/2.90  thf(t39_xboole_1, axiom,
% 2.67/2.90    (![A:$i,B:$i]:
% 2.67/2.90     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.67/2.90  thf('84', plain,
% 2.67/2.90      (![X24 : $i, X25 : $i]:
% 2.67/2.90         ((k2_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24))
% 2.67/2.90           = (k2_xboole_0 @ X24 @ X25))),
% 2.67/2.90      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.67/2.90  thf('85', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.67/2.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.67/2.90  thf(t73_xboole_1, axiom,
% 2.67/2.90    (![A:$i,B:$i,C:$i]:
% 2.67/2.90     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 2.67/2.90       ( r1_tarski @ A @ B ) ))).
% 2.67/2.90  thf('86', plain,
% 2.67/2.90      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.67/2.90         ((r1_tarski @ X26 @ X27)
% 2.67/2.90          | ~ (r1_tarski @ X26 @ (k2_xboole_0 @ X27 @ X28))
% 2.67/2.90          | ~ (r1_xboole_0 @ X26 @ X28))),
% 2.67/2.90      inference('cnf', [status(esa)], [t73_xboole_1])).
% 2.67/2.90  thf('87', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.90         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 2.67/2.90          | ~ (r1_xboole_0 @ X2 @ X1)
% 2.67/2.90          | (r1_tarski @ X2 @ X0))),
% 2.67/2.90      inference('sup-', [status(thm)], ['85', '86'])).
% 2.67/2.90  thf('88', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.90         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 2.67/2.90          | (r1_tarski @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 2.67/2.90          | ~ (r1_xboole_0 @ X2 @ X1))),
% 2.67/2.90      inference('sup-', [status(thm)], ['84', '87'])).
% 2.67/2.90  thf('89', plain,
% 2.67/2.90      (![X0 : $i]:
% 2.67/2.90         (~ (r1_xboole_0 @ sk_C_1 @ X0)
% 2.67/2.90          | (r1_tarski @ sk_C_1 @ (k4_xboole_0 @ sk_A @ X0)))),
% 2.67/2.90      inference('sup-', [status(thm)], ['83', '88'])).
% 2.67/2.90  thf('90', plain,
% 2.67/2.90      ((r1_tarski @ sk_C_1 @ 
% 2.67/2.90        (k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 2.67/2.90      inference('sup-', [status(thm)], ['76', '89'])).
% 2.67/2.90  thf('91', plain,
% 2.67/2.90      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 2.67/2.90         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 2.67/2.90      inference('demod', [status(thm)], ['67', '68'])).
% 2.67/2.90  thf('92', plain,
% 2.67/2.90      ((r1_tarski @ sk_C_1 @ 
% 2.67/2.90        (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 2.67/2.90      inference('demod', [status(thm)], ['90', '91'])).
% 2.67/2.90  thf('93', plain,
% 2.67/2.90      (![X6 : $i, X8 : $i]:
% 2.67/2.90         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 2.67/2.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.67/2.90  thf('94', plain,
% 2.67/2.90      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1)) @ 
% 2.67/2.90           sk_C_1)
% 2.67/2.90        | ((k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1)) = (sk_C_1)))),
% 2.67/2.90      inference('sup-', [status(thm)], ['92', '93'])).
% 2.67/2.90  thf('95', plain,
% 2.67/2.90      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.67/2.90      inference('sup+', [status(thm)], ['11', '14'])).
% 2.67/2.90  thf('96', plain,
% 2.67/2.90      (![X24 : $i, X25 : $i]:
% 2.67/2.90         ((k2_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24))
% 2.67/2.90           = (k2_xboole_0 @ X24 @ X25))),
% 2.67/2.90      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.67/2.90  thf('97', plain,
% 2.67/2.90      (((k2_xboole_0 @ sk_C_1 @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 2.67/2.90         = (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 2.67/2.90      inference('sup+', [status(thm)], ['95', '96'])).
% 2.67/2.90  thf('98', plain, (((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 2.67/2.90      inference('sup-', [status(thm)], ['78', '79'])).
% 2.67/2.90  thf('99', plain,
% 2.67/2.90      (((k2_xboole_0 @ sk_C_1 @ (k5_xboole_0 @ sk_A @ sk_C_1)) = (sk_A))),
% 2.67/2.90      inference('demod', [status(thm)], ['97', '98'])).
% 2.67/2.90  thf('100', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 2.67/2.90      inference('sup-', [status(thm)], ['71', '72'])).
% 2.67/2.90  thf('101', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 2.67/2.90      inference('sup-', [status(thm)], ['50', '51'])).
% 2.67/2.90  thf('102', plain,
% 2.67/2.90      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.67/2.90         ((r1_tarski @ X26 @ X27)
% 2.67/2.90          | ~ (r1_tarski @ X26 @ (k2_xboole_0 @ X27 @ X28))
% 2.67/2.90          | ~ (r1_xboole_0 @ X26 @ X28))),
% 2.67/2.90      inference('cnf', [status(esa)], [t73_xboole_1])).
% 2.67/2.90  thf('103', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.90         (~ (r1_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X0)
% 2.67/2.90          | (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X1))),
% 2.67/2.90      inference('sup-', [status(thm)], ['101', '102'])).
% 2.67/2.90  thf('104', plain,
% 2.67/2.90      (![X0 : $i, X1 : $i]:
% 2.67/2.90         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) @ X1)),
% 2.67/2.90      inference('sup-', [status(thm)], ['100', '103'])).
% 2.67/2.91  thf('105', plain,
% 2.67/2.91      (![X0 : $i, X1 : $i]:
% 2.67/2.91         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 2.67/2.91           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 2.67/2.91      inference('sup+', [status(thm)], ['64', '65'])).
% 2.67/2.91  thf('106', plain,
% 2.67/2.91      (![X0 : $i, X1 : $i]:
% 2.67/2.91         (r1_tarski @ (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) @ X1)),
% 2.67/2.91      inference('demod', [status(thm)], ['104', '105'])).
% 2.67/2.91  thf('107', plain,
% 2.67/2.91      ((r1_tarski @ (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1)) @ 
% 2.67/2.91        sk_C_1)),
% 2.67/2.91      inference('sup+', [status(thm)], ['99', '106'])).
% 2.67/2.91  thf('108', plain,
% 2.67/2.91      (((k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1)) = (sk_C_1))),
% 2.67/2.91      inference('demod', [status(thm)], ['94', '107'])).
% 2.67/2.91  thf('109', plain,
% 2.67/2.91      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1)) = (sk_C_1))),
% 2.67/2.91      inference('demod', [status(thm)], ['69', '108'])).
% 2.67/2.91  thf('110', plain,
% 2.67/2.91      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.67/2.91      inference('sup+', [status(thm)], ['33', '36'])).
% 2.67/2.91  thf('111', plain,
% 2.67/2.91      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.91         (k3_subset_1 @ sk_A @ sk_B)))
% 2.67/2.91         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.91               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.67/2.91      inference('split', [status(esa)], ['16'])).
% 2.67/2.91  thf('112', plain,
% 2.67/2.91      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 2.67/2.91      inference('sup-', [status(thm)], ['39', '40'])).
% 2.67/2.91  thf('113', plain,
% 2.67/2.91      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.67/2.91         ((r1_xboole_0 @ X11 @ X13)
% 2.67/2.91          | ~ (r1_tarski @ X11 @ (k4_xboole_0 @ X12 @ X13)))),
% 2.67/2.91      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.67/2.91  thf('114', plain,
% 2.67/2.91      (![X0 : $i]:
% 2.67/2.91         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 2.67/2.91          | (r1_xboole_0 @ X0 @ sk_B))),
% 2.67/2.91      inference('sup-', [status(thm)], ['112', '113'])).
% 2.67/2.91  thf('115', plain,
% 2.67/2.91      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))
% 2.67/2.91         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.91               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.67/2.91      inference('sup-', [status(thm)], ['111', '114'])).
% 2.67/2.91  thf('116', plain,
% 2.67/2.91      (![X4 : $i, X5 : $i]:
% 2.67/2.91         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 2.67/2.91      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.67/2.91  thf('117', plain,
% 2.67/2.91      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 2.67/2.91         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.91               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.67/2.91      inference('sup-', [status(thm)], ['115', '116'])).
% 2.67/2.91  thf('118', plain,
% 2.67/2.91      (((r1_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1)))
% 2.67/2.91         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.91               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.67/2.91      inference('sup+', [status(thm)], ['110', '117'])).
% 2.67/2.91  thf('119', plain,
% 2.67/2.91      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.67/2.91      inference('sup-', [status(thm)], ['58', '61'])).
% 2.67/2.91  thf('120', plain, ((r1_tarski @ sk_B @ sk_A)),
% 2.67/2.91      inference('sup-', [status(thm)], ['25', '26'])).
% 2.67/2.91  thf('121', plain,
% 2.67/2.91      (![X17 : $i, X18 : $i]:
% 2.67/2.91         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 2.67/2.91      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.67/2.91  thf('122', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 2.67/2.91      inference('sup-', [status(thm)], ['120', '121'])).
% 2.67/2.91  thf('123', plain,
% 2.67/2.91      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.67/2.91         ((r1_tarski @ X14 @ X15)
% 2.67/2.91          | ~ (r1_tarski @ (k2_xboole_0 @ X14 @ X16) @ X15))),
% 2.67/2.91      inference('cnf', [status(esa)], [t11_xboole_1])).
% 2.67/2.91  thf('124', plain,
% 2.67/2.91      (![X0 : $i]: (~ (r1_tarski @ sk_A @ X0) | (r1_tarski @ sk_B @ X0))),
% 2.67/2.91      inference('sup-', [status(thm)], ['122', '123'])).
% 2.67/2.91  thf('125', plain,
% 2.67/2.91      (![X0 : $i]: (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ sk_A))),
% 2.67/2.91      inference('sup-', [status(thm)], ['119', '124'])).
% 2.67/2.91  thf('126', plain,
% 2.67/2.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.91         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 2.67/2.91          | (r1_tarski @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 2.67/2.91          | ~ (r1_xboole_0 @ X2 @ X1))),
% 2.67/2.91      inference('sup-', [status(thm)], ['84', '87'])).
% 2.67/2.91  thf('127', plain,
% 2.67/2.91      (![X0 : $i]:
% 2.67/2.91         (~ (r1_xboole_0 @ sk_B @ X0)
% 2.67/2.91          | (r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ X0)))),
% 2.67/2.91      inference('sup-', [status(thm)], ['125', '126'])).
% 2.67/2.91  thf('128', plain,
% 2.67/2.91      (((r1_tarski @ sk_B @ 
% 2.67/2.91         (k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1))))
% 2.67/2.91         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.91               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.67/2.91      inference('sup-', [status(thm)], ['118', '127'])).
% 2.67/2.91  thf('129', plain,
% 2.67/2.91      (((r1_tarski @ sk_B @ sk_C_1))
% 2.67/2.91         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.91               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.67/2.91      inference('sup+', [status(thm)], ['109', '128'])).
% 2.67/2.91  thf('130', plain,
% 2.67/2.91      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 2.67/2.91      inference('split', [status(esa)], ['0'])).
% 2.67/2.91  thf('131', plain,
% 2.67/2.91      (~
% 2.67/2.91       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.91         (k3_subset_1 @ sk_A @ sk_B))) | 
% 2.67/2.91       ((r1_tarski @ sk_B @ sk_C_1))),
% 2.67/2.91      inference('sup-', [status(thm)], ['129', '130'])).
% 2.67/2.91  thf('132', plain, ($false),
% 2.67/2.91      inference('sat_resolution*', [status(thm)], ['1', '46', '47', '131'])).
% 2.67/2.91  
% 2.67/2.91  % SZS output end Refutation
% 2.67/2.91  
% 2.67/2.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
