%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nNNfqUtv6u

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:11 EST 2020

% Result     : Theorem 2.31s
% Output     : Refutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 540 expanded)
%              Number of leaves         :   29 ( 171 expanded)
%              Depth                    :   24
%              Number of atoms          :  876 (4689 expanded)
%              Number of equality atoms :   47 ( 218 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ X32 )
      | ( r2_hidden @ X31 @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X36: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ( r1_tarski @ X29 @ X27 )
      | ( X28
       != ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('8',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r1_tarski @ X29 @ X27 )
      | ~ ( r2_hidden @ X29 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
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

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ X32 )
      | ( r2_hidden @ X31 @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X36: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('24',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r1_tarski @ X29 @ X27 )
      | ~ ( r2_hidden @ X29 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('26',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('33',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','19','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('38',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['37','39'])).

thf('41',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('42',plain,
    ( ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('44',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r1_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('48',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('49',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('50',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
      = sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t33_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('52',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ ( k4_xboole_0 @ X15 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t33_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('56',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('59',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('60',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','62'])).

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

thf('68',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['38'])).

thf('69',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['38'])).

thf('70',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['36','65','69'])).

thf('71',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['68','70'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('72',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('73',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['71','82'])).

thf('84',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_B )
      = ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('89',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('90',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ ( k4_xboole_0 @ X15 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t33_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['88','91'])).

thf('93',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['87','92'])).

thf('94',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('95',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['67','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.08  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nNNfqUtv6u
% 0.08/0.28  % Computer   : n019.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % DateTime   : Tue Dec  1 13:14:07 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.08/0.28  % Running portfolio for 600 s
% 0.08/0.28  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.08/0.28  % Number of cores: 8
% 0.08/0.28  % Python version: Python 3.6.8
% 0.08/0.29  % Running in FO mode
% 2.31/2.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.31/2.58  % Solved by: fo/fo7.sh
% 2.31/2.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.31/2.58  % done 5187 iterations in 2.188s
% 2.31/2.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.31/2.58  % SZS output start Refutation
% 2.31/2.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.31/2.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.31/2.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.31/2.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.31/2.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.31/2.58  thf(sk_B_type, type, sk_B: $i).
% 2.31/2.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.31/2.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.31/2.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.31/2.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.31/2.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.31/2.58  thf(sk_A_type, type, sk_A: $i).
% 2.31/2.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.31/2.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.31/2.58  thf(t31_subset_1, conjecture,
% 2.31/2.58    (![A:$i,B:$i]:
% 2.31/2.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.31/2.58       ( ![C:$i]:
% 2.31/2.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.31/2.58           ( ( r1_tarski @ B @ C ) <=>
% 2.31/2.58             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 2.31/2.58  thf(zf_stmt_0, negated_conjecture,
% 2.31/2.58    (~( ![A:$i,B:$i]:
% 2.31/2.58        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.31/2.58          ( ![C:$i]:
% 2.31/2.58            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.31/2.58              ( ( r1_tarski @ B @ C ) <=>
% 2.31/2.58                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 2.31/2.58    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 2.31/2.58  thf('0', plain,
% 2.31/2.58      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.31/2.58           (k3_subset_1 @ sk_A @ sk_B))
% 2.31/2.58        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 2.31/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.58  thf('1', plain,
% 2.31/2.58      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.31/2.58           (k3_subset_1 @ sk_A @ sk_B)))
% 2.31/2.58         <= (~
% 2.31/2.58             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.31/2.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.31/2.58      inference('split', [status(esa)], ['0'])).
% 2.31/2.58  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.31/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.58  thf(d2_subset_1, axiom,
% 2.31/2.58    (![A:$i,B:$i]:
% 2.31/2.58     ( ( ( v1_xboole_0 @ A ) =>
% 2.31/2.58         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 2.31/2.58       ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.31/2.58         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 2.31/2.58  thf('3', plain,
% 2.31/2.58      (![X31 : $i, X32 : $i]:
% 2.31/2.58         (~ (m1_subset_1 @ X31 @ X32)
% 2.31/2.58          | (r2_hidden @ X31 @ X32)
% 2.31/2.58          | (v1_xboole_0 @ X32))),
% 2.31/2.58      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.31/2.58  thf('4', plain,
% 2.31/2.58      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 2.31/2.58        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 2.31/2.58      inference('sup-', [status(thm)], ['2', '3'])).
% 2.31/2.58  thf(fc1_subset_1, axiom,
% 2.31/2.58    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.31/2.58  thf('5', plain, (![X36 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 2.31/2.58      inference('cnf', [status(esa)], [fc1_subset_1])).
% 2.31/2.58  thf('6', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.31/2.58      inference('clc', [status(thm)], ['4', '5'])).
% 2.31/2.58  thf(d1_zfmisc_1, axiom,
% 2.31/2.58    (![A:$i,B:$i]:
% 2.31/2.58     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 2.31/2.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 2.31/2.58  thf('7', plain,
% 2.31/2.58      (![X27 : $i, X28 : $i, X29 : $i]:
% 2.31/2.58         (~ (r2_hidden @ X29 @ X28)
% 2.31/2.58          | (r1_tarski @ X29 @ X27)
% 2.31/2.58          | ((X28) != (k1_zfmisc_1 @ X27)))),
% 2.31/2.58      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 2.31/2.58  thf('8', plain,
% 2.31/2.58      (![X27 : $i, X29 : $i]:
% 2.31/2.58         ((r1_tarski @ X29 @ X27) | ~ (r2_hidden @ X29 @ (k1_zfmisc_1 @ X27)))),
% 2.31/2.58      inference('simplify', [status(thm)], ['7'])).
% 2.31/2.58  thf('9', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 2.31/2.58      inference('sup-', [status(thm)], ['6', '8'])).
% 2.31/2.58  thf(t28_xboole_1, axiom,
% 2.31/2.58    (![A:$i,B:$i]:
% 2.31/2.58     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.31/2.58  thf('10', plain,
% 2.31/2.58      (![X12 : $i, X13 : $i]:
% 2.31/2.58         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 2.31/2.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.31/2.58  thf('11', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 2.31/2.58      inference('sup-', [status(thm)], ['9', '10'])).
% 2.31/2.58  thf(commutativity_k3_xboole_0, axiom,
% 2.31/2.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.31/2.58  thf('12', plain,
% 2.31/2.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.31/2.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.31/2.58  thf(t100_xboole_1, axiom,
% 2.31/2.58    (![A:$i,B:$i]:
% 2.31/2.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.31/2.58  thf('13', plain,
% 2.31/2.58      (![X7 : $i, X8 : $i]:
% 2.31/2.58         ((k4_xboole_0 @ X7 @ X8)
% 2.31/2.58           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 2.31/2.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.31/2.58  thf('14', plain,
% 2.31/2.58      (![X0 : $i, X1 : $i]:
% 2.31/2.58         ((k4_xboole_0 @ X0 @ X1)
% 2.31/2.58           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.31/2.58      inference('sup+', [status(thm)], ['12', '13'])).
% 2.31/2.58  thf('15', plain,
% 2.31/2.58      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.31/2.58      inference('sup+', [status(thm)], ['11', '14'])).
% 2.31/2.58  thf('16', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.31/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.58  thf(d5_subset_1, axiom,
% 2.31/2.58    (![A:$i,B:$i]:
% 2.31/2.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.31/2.58       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.31/2.58  thf('17', plain,
% 2.31/2.58      (![X34 : $i, X35 : $i]:
% 2.31/2.58         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 2.31/2.58          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 2.31/2.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.31/2.58  thf('18', plain,
% 2.31/2.58      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 2.31/2.58      inference('sup-', [status(thm)], ['16', '17'])).
% 2.31/2.58  thf('19', plain,
% 2.31/2.58      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.31/2.58      inference('sup+', [status(thm)], ['15', '18'])).
% 2.31/2.58  thf('20', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.31/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.58  thf('21', plain,
% 2.31/2.58      (![X31 : $i, X32 : $i]:
% 2.31/2.58         (~ (m1_subset_1 @ X31 @ X32)
% 2.31/2.58          | (r2_hidden @ X31 @ X32)
% 2.31/2.58          | (v1_xboole_0 @ X32))),
% 2.31/2.58      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.31/2.58  thf('22', plain,
% 2.31/2.58      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 2.31/2.58        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 2.31/2.58      inference('sup-', [status(thm)], ['20', '21'])).
% 2.31/2.58  thf('23', plain, (![X36 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 2.31/2.58      inference('cnf', [status(esa)], [fc1_subset_1])).
% 2.31/2.58  thf('24', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.31/2.58      inference('clc', [status(thm)], ['22', '23'])).
% 2.31/2.58  thf('25', plain,
% 2.31/2.58      (![X27 : $i, X29 : $i]:
% 2.31/2.58         ((r1_tarski @ X29 @ X27) | ~ (r2_hidden @ X29 @ (k1_zfmisc_1 @ X27)))),
% 2.31/2.58      inference('simplify', [status(thm)], ['7'])).
% 2.31/2.58  thf('26', plain, ((r1_tarski @ sk_B @ sk_A)),
% 2.31/2.58      inference('sup-', [status(thm)], ['24', '25'])).
% 2.31/2.58  thf('27', plain,
% 2.31/2.58      (![X12 : $i, X13 : $i]:
% 2.31/2.58         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 2.31/2.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.31/2.58  thf('28', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 2.31/2.58      inference('sup-', [status(thm)], ['26', '27'])).
% 2.31/2.58  thf('29', plain,
% 2.31/2.58      (![X0 : $i, X1 : $i]:
% 2.31/2.58         ((k4_xboole_0 @ X0 @ X1)
% 2.31/2.58           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.31/2.58      inference('sup+', [status(thm)], ['12', '13'])).
% 2.31/2.58  thf('30', plain,
% 2.31/2.58      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 2.31/2.58      inference('sup+', [status(thm)], ['28', '29'])).
% 2.31/2.58  thf('31', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.31/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.58  thf('32', plain,
% 2.31/2.58      (![X34 : $i, X35 : $i]:
% 2.31/2.58         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 2.31/2.58          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 2.31/2.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.31/2.58  thf('33', plain,
% 2.31/2.58      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 2.31/2.58      inference('sup-', [status(thm)], ['31', '32'])).
% 2.31/2.58  thf('34', plain,
% 2.31/2.58      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 2.31/2.58      inference('sup+', [status(thm)], ['30', '33'])).
% 2.31/2.58  thf('35', plain,
% 2.31/2.58      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 2.31/2.58           (k5_xboole_0 @ sk_A @ sk_B)))
% 2.31/2.58         <= (~
% 2.31/2.58             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.31/2.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.31/2.58      inference('demod', [status(thm)], ['1', '19', '34'])).
% 2.31/2.58  thf('36', plain,
% 2.31/2.58      (~
% 2.31/2.58       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.31/2.58         (k3_subset_1 @ sk_A @ sk_B))) | 
% 2.31/2.58       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 2.31/2.58      inference('split', [status(esa)], ['0'])).
% 2.31/2.58  thf('37', plain,
% 2.31/2.58      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 2.31/2.58      inference('sup+', [status(thm)], ['30', '33'])).
% 2.31/2.58  thf('38', plain,
% 2.31/2.58      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.31/2.58         (k3_subset_1 @ sk_A @ sk_B))
% 2.31/2.58        | (r1_tarski @ sk_B @ sk_C_1))),
% 2.31/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.58  thf('39', plain,
% 2.31/2.58      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.31/2.58         (k3_subset_1 @ sk_A @ sk_B)))
% 2.31/2.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.31/2.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.31/2.58      inference('split', [status(esa)], ['38'])).
% 2.31/2.58  thf('40', plain,
% 2.31/2.58      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.31/2.58         (k5_xboole_0 @ sk_A @ sk_B)))
% 2.31/2.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.31/2.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.31/2.58      inference('sup+', [status(thm)], ['37', '39'])).
% 2.31/2.58  thf('41', plain,
% 2.31/2.58      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.31/2.58      inference('sup+', [status(thm)], ['15', '18'])).
% 2.31/2.58  thf('42', plain,
% 2.31/2.58      (((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 2.31/2.58         (k5_xboole_0 @ sk_A @ sk_B)))
% 2.31/2.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.31/2.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.31/2.58      inference('demod', [status(thm)], ['40', '41'])).
% 2.31/2.58  thf('43', plain,
% 2.31/2.58      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 2.31/2.58      inference('sup+', [status(thm)], ['28', '29'])).
% 2.31/2.58  thf(t106_xboole_1, axiom,
% 2.31/2.58    (![A:$i,B:$i,C:$i]:
% 2.31/2.58     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 2.31/2.58       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 2.31/2.58  thf('44', plain,
% 2.31/2.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.31/2.58         ((r1_xboole_0 @ X9 @ X11)
% 2.31/2.58          | ~ (r1_tarski @ X9 @ (k4_xboole_0 @ X10 @ X11)))),
% 2.31/2.58      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.31/2.58  thf('45', plain,
% 2.31/2.58      (![X0 : $i]:
% 2.31/2.58         (~ (r1_tarski @ X0 @ (k5_xboole_0 @ sk_A @ sk_B))
% 2.31/2.58          | (r1_xboole_0 @ X0 @ sk_B))),
% 2.31/2.58      inference('sup-', [status(thm)], ['43', '44'])).
% 2.31/2.58  thf('46', plain,
% 2.31/2.58      (((r1_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_B))
% 2.31/2.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.31/2.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.31/2.58      inference('sup-', [status(thm)], ['42', '45'])).
% 2.31/2.58  thf(symmetry_r1_xboole_0, axiom,
% 2.31/2.58    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.31/2.58  thf('47', plain,
% 2.31/2.58      (![X2 : $i, X3 : $i]:
% 2.31/2.58         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.31/2.58      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.31/2.58  thf('48', plain,
% 2.31/2.58      (((r1_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1)))
% 2.31/2.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.31/2.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.31/2.58      inference('sup-', [status(thm)], ['46', '47'])).
% 2.31/2.58  thf(t83_xboole_1, axiom,
% 2.31/2.58    (![A:$i,B:$i]:
% 2.31/2.58     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.31/2.58  thf('49', plain,
% 2.31/2.58      (![X23 : $i, X24 : $i]:
% 2.31/2.58         (((k4_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_xboole_0 @ X23 @ X24))),
% 2.31/2.58      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.31/2.58  thf('50', plain,
% 2.31/2.58      ((((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1)) = (sk_B)))
% 2.31/2.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.31/2.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.31/2.58      inference('sup-', [status(thm)], ['48', '49'])).
% 2.31/2.58  thf('51', plain, ((r1_tarski @ sk_B @ sk_A)),
% 2.31/2.58      inference('sup-', [status(thm)], ['24', '25'])).
% 2.31/2.58  thf(t33_xboole_1, axiom,
% 2.31/2.58    (![A:$i,B:$i,C:$i]:
% 2.31/2.58     ( ( r1_tarski @ A @ B ) =>
% 2.31/2.58       ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 2.31/2.58  thf('52', plain,
% 2.31/2.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.31/2.58         (~ (r1_tarski @ X15 @ X16)
% 2.31/2.58          | (r1_tarski @ (k4_xboole_0 @ X15 @ X17) @ (k4_xboole_0 @ X16 @ X17)))),
% 2.31/2.58      inference('cnf', [status(esa)], [t33_xboole_1])).
% 2.31/2.58  thf('53', plain,
% 2.31/2.58      (![X0 : $i]:
% 2.31/2.58         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (k4_xboole_0 @ sk_A @ X0))),
% 2.31/2.58      inference('sup-', [status(thm)], ['51', '52'])).
% 2.31/2.58  thf('54', plain,
% 2.31/2.58      (((r1_tarski @ sk_B @ 
% 2.31/2.58         (k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1))))
% 2.31/2.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.31/2.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.31/2.58      inference('sup+', [status(thm)], ['50', '53'])).
% 2.31/2.58  thf('55', plain,
% 2.31/2.58      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 2.31/2.58      inference('sup-', [status(thm)], ['16', '17'])).
% 2.31/2.58  thf(t48_xboole_1, axiom,
% 2.31/2.58    (![A:$i,B:$i]:
% 2.31/2.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.31/2.58  thf('56', plain,
% 2.31/2.58      (![X21 : $i, X22 : $i]:
% 2.31/2.58         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 2.31/2.58           = (k3_xboole_0 @ X21 @ X22))),
% 2.31/2.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.31/2.58  thf('57', plain,
% 2.31/2.58      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1))
% 2.31/2.58         = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 2.31/2.58      inference('sup+', [status(thm)], ['55', '56'])).
% 2.31/2.58  thf('58', plain,
% 2.31/2.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.31/2.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.31/2.58  thf('59', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 2.31/2.58      inference('sup-', [status(thm)], ['9', '10'])).
% 2.31/2.58  thf('60', plain,
% 2.31/2.58      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1)) = (sk_C_1))),
% 2.31/2.58      inference('demod', [status(thm)], ['57', '58', '59'])).
% 2.31/2.58  thf('61', plain,
% 2.31/2.58      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.31/2.58      inference('sup+', [status(thm)], ['15', '18'])).
% 2.31/2.58  thf('62', plain,
% 2.31/2.58      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1)) = (sk_C_1))),
% 2.31/2.58      inference('demod', [status(thm)], ['60', '61'])).
% 2.31/2.58  thf('63', plain,
% 2.31/2.58      (((r1_tarski @ sk_B @ sk_C_1))
% 2.31/2.58         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.31/2.58               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.31/2.58      inference('demod', [status(thm)], ['54', '62'])).
% 2.31/2.58  thf('64', plain,
% 2.31/2.58      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 2.31/2.58      inference('split', [status(esa)], ['0'])).
% 2.31/2.58  thf('65', plain,
% 2.31/2.58      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 2.31/2.58       ~
% 2.31/2.58       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.31/2.58         (k3_subset_1 @ sk_A @ sk_B)))),
% 2.31/2.58      inference('sup-', [status(thm)], ['63', '64'])).
% 2.31/2.58  thf('66', plain,
% 2.31/2.58      (~
% 2.31/2.58       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.31/2.58         (k3_subset_1 @ sk_A @ sk_B)))),
% 2.31/2.58      inference('sat_resolution*', [status(thm)], ['36', '65'])).
% 2.31/2.58  thf('67', plain,
% 2.31/2.58      (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 2.31/2.58          (k5_xboole_0 @ sk_A @ sk_B))),
% 2.31/2.58      inference('simpl_trail', [status(thm)], ['35', '66'])).
% 2.31/2.58  thf('68', plain,
% 2.31/2.58      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 2.31/2.58      inference('split', [status(esa)], ['38'])).
% 2.31/2.58  thf('69', plain,
% 2.31/2.58      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 2.31/2.58       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.31/2.58         (k3_subset_1 @ sk_A @ sk_B)))),
% 2.31/2.58      inference('split', [status(esa)], ['38'])).
% 2.31/2.58  thf('70', plain, (((r1_tarski @ sk_B @ sk_C_1))),
% 2.31/2.58      inference('sat_resolution*', [status(thm)], ['36', '65', '69'])).
% 2.31/2.58  thf('71', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 2.31/2.58      inference('simpl_trail', [status(thm)], ['68', '70'])).
% 2.31/2.58  thf(t3_boole, axiom,
% 2.31/2.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.31/2.58  thf('72', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 2.31/2.58      inference('cnf', [status(esa)], [t3_boole])).
% 2.31/2.58  thf(t36_xboole_1, axiom,
% 2.31/2.58    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.31/2.58  thf('73', plain,
% 2.31/2.58      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 2.31/2.58      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.31/2.58  thf('74', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.31/2.58      inference('sup+', [status(thm)], ['72', '73'])).
% 2.31/2.58  thf('75', plain,
% 2.31/2.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.31/2.58         ((r1_xboole_0 @ X9 @ X11)
% 2.31/2.58          | ~ (r1_tarski @ X9 @ (k4_xboole_0 @ X10 @ X11)))),
% 2.31/2.58      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.31/2.58  thf('76', plain,
% 2.31/2.58      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 2.31/2.58      inference('sup-', [status(thm)], ['74', '75'])).
% 2.31/2.58  thf('77', plain,
% 2.31/2.58      (![X2 : $i, X3 : $i]:
% 2.31/2.58         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.31/2.58      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.31/2.58  thf('78', plain,
% 2.31/2.58      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.31/2.58      inference('sup-', [status(thm)], ['76', '77'])).
% 2.31/2.58  thf('79', plain,
% 2.31/2.58      (![X23 : $i, X24 : $i]:
% 2.31/2.58         (((k4_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_xboole_0 @ X23 @ X24))),
% 2.31/2.58      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.31/2.58  thf('80', plain,
% 2.31/2.58      (![X0 : $i, X1 : $i]:
% 2.31/2.58         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 2.31/2.58      inference('sup-', [status(thm)], ['78', '79'])).
% 2.31/2.58  thf('81', plain,
% 2.31/2.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.31/2.58         ((r1_xboole_0 @ X9 @ X11)
% 2.31/2.58          | ~ (r1_tarski @ X9 @ (k4_xboole_0 @ X10 @ X11)))),
% 2.31/2.58      inference('cnf', [status(esa)], [t106_xboole_1])).
% 2.31/2.58  thf('82', plain,
% 2.31/2.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.58         (~ (r1_tarski @ X2 @ X0)
% 2.31/2.58          | (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.31/2.58      inference('sup-', [status(thm)], ['80', '81'])).
% 2.31/2.58  thf('83', plain,
% 2.31/2.58      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1))),
% 2.31/2.58      inference('sup-', [status(thm)], ['71', '82'])).
% 2.31/2.58  thf('84', plain,
% 2.31/2.58      (![X23 : $i, X24 : $i]:
% 2.31/2.58         (((k4_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_xboole_0 @ X23 @ X24))),
% 2.31/2.58      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.31/2.58  thf('85', plain,
% 2.31/2.58      (![X0 : $i]:
% 2.31/2.58         ((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1)) = (sk_B))),
% 2.31/2.58      inference('sup-', [status(thm)], ['83', '84'])).
% 2.31/2.58  thf('86', plain,
% 2.31/2.58      (![X0 : $i, X1 : $i]:
% 2.31/2.58         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 2.31/2.58      inference('sup-', [status(thm)], ['78', '79'])).
% 2.31/2.58  thf('87', plain,
% 2.31/2.58      (![X0 : $i]:
% 2.31/2.58         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_B)
% 2.31/2.58           = (k4_xboole_0 @ X0 @ sk_C_1))),
% 2.31/2.58      inference('sup+', [status(thm)], ['85', '86'])).
% 2.31/2.58  thf('88', plain,
% 2.31/2.58      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 2.31/2.58      inference('sup+', [status(thm)], ['28', '29'])).
% 2.31/2.58  thf('89', plain,
% 2.31/2.58      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 2.31/2.58      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.31/2.58  thf('90', plain,
% 2.31/2.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.31/2.58         (~ (r1_tarski @ X15 @ X16)
% 2.31/2.58          | (r1_tarski @ (k4_xboole_0 @ X15 @ X17) @ (k4_xboole_0 @ X16 @ X17)))),
% 2.31/2.58      inference('cnf', [status(esa)], [t33_xboole_1])).
% 2.31/2.58  thf('91', plain,
% 2.31/2.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.58         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2) @ 
% 2.31/2.58          (k4_xboole_0 @ X0 @ X2))),
% 2.31/2.58      inference('sup-', [status(thm)], ['89', '90'])).
% 2.31/2.58  thf('92', plain,
% 2.31/2.58      (![X0 : $i]:
% 2.31/2.58         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B) @ 
% 2.31/2.58          (k5_xboole_0 @ sk_A @ sk_B))),
% 2.31/2.58      inference('sup+', [status(thm)], ['88', '91'])).
% 2.31/2.58  thf('93', plain,
% 2.31/2.58      ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ (k5_xboole_0 @ sk_A @ sk_B))),
% 2.31/2.58      inference('sup+', [status(thm)], ['87', '92'])).
% 2.31/2.58  thf('94', plain,
% 2.31/2.58      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.31/2.58      inference('sup+', [status(thm)], ['11', '14'])).
% 2.31/2.58  thf('95', plain,
% 2.31/2.58      ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ (k5_xboole_0 @ sk_A @ sk_B))),
% 2.31/2.58      inference('demod', [status(thm)], ['93', '94'])).
% 2.31/2.58  thf('96', plain, ($false), inference('demod', [status(thm)], ['67', '95'])).
% 2.31/2.58  
% 2.31/2.58  % SZS output end Refutation
% 2.31/2.58  
% 2.31/2.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
