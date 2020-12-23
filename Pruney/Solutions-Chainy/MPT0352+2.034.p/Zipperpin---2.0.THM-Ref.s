%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PfdPOF6epE

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:12 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 161 expanded)
%              Number of leaves         :   31 (  58 expanded)
%              Depth                    :   16
%              Number of atoms          :  754 (1363 expanded)
%              Number of equality atoms :   36 (  48 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X35 @ X36 )
        = ( k4_xboole_0 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ ( k4_xboole_0 @ X16 @ X15 ) @ ( k4_xboole_0 @ X16 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('8',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X35 @ X36 )
        = ( k4_xboole_0 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ X33 )
      | ( r2_hidden @ X32 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X37: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('26',plain,(
    r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('27',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ X29 @ ( k3_tarski @ X30 ) )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('28',plain,(
    r1_tarski @ sk_C @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('29',plain,(
    ! [X31: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('30',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['28','29'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('35',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X22 @ X23 )
      | ~ ( r1_tarski @ X22 @ X23 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('39',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('43',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('44',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['21','44'])).

thf('46',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('47',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ ( k4_xboole_0 @ X16 @ X15 ) @ ( k4_xboole_0 @ X16 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('48',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ sk_C )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('51',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('54',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ X33 )
      | ( r2_hidden @ X32 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X37: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('59',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ X29 @ ( k3_tarski @ X30 ) )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('61',plain,(
    r1_tarski @ sk_B @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X31: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('63',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['61','62'])).

thf(t33_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('64',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ ( k4_xboole_0 @ X11 @ X13 ) @ ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t33_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('66',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('69',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('71',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('75',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['54','75'])).

thf('77',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','76'])).

thf('78',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
   <= ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('79',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','15','16','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PfdPOF6epE
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:33:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.62/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.81  % Solved by: fo/fo7.sh
% 0.62/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.81  % done 1064 iterations in 0.346s
% 0.62/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.81  % SZS output start Refutation
% 0.62/0.81  thf(sk_C_type, type, sk_C: $i).
% 0.62/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.62/0.81  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.62/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.81  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.62/0.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.62/0.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.62/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.62/0.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.62/0.81  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.62/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.62/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.62/0.81  thf(t31_subset_1, conjecture,
% 0.62/0.81    (![A:$i,B:$i]:
% 0.62/0.81     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.62/0.81       ( ![C:$i]:
% 0.62/0.81         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.62/0.81           ( ( r1_tarski @ B @ C ) <=>
% 0.62/0.81             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.62/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.81    (~( ![A:$i,B:$i]:
% 0.62/0.81        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.62/0.81          ( ![C:$i]:
% 0.62/0.81            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.62/0.81              ( ( r1_tarski @ B @ C ) <=>
% 0.62/0.81                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.62/0.81    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.62/0.81  thf('0', plain,
% 0.62/0.81      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.62/0.81           (k3_subset_1 @ sk_A @ sk_B))
% 0.62/0.81        | ~ (r1_tarski @ sk_B @ sk_C))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('1', plain,
% 0.62/0.81      (~
% 0.62/0.81       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.62/0.81       ~ ((r1_tarski @ sk_B @ sk_C))),
% 0.62/0.81      inference('split', [status(esa)], ['0'])).
% 0.62/0.81  thf('2', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf(d5_subset_1, axiom,
% 0.62/0.81    (![A:$i,B:$i]:
% 0.62/0.81     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.62/0.81       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.62/0.81  thf('3', plain,
% 0.62/0.81      (![X35 : $i, X36 : $i]:
% 0.62/0.81         (((k3_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))
% 0.62/0.81          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35)))),
% 0.62/0.81      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.62/0.81  thf('4', plain,
% 0.62/0.81      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.62/0.81      inference('sup-', [status(thm)], ['2', '3'])).
% 0.62/0.81  thf('5', plain,
% 0.62/0.81      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))
% 0.62/0.81        | (r1_tarski @ sk_B @ sk_C))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('6', plain,
% 0.62/0.81      (((r1_tarski @ sk_B @ sk_C)) <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.62/0.81      inference('split', [status(esa)], ['5'])).
% 0.62/0.81  thf(t34_xboole_1, axiom,
% 0.62/0.81    (![A:$i,B:$i,C:$i]:
% 0.62/0.81     ( ( r1_tarski @ A @ B ) =>
% 0.62/0.81       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.62/0.81  thf('7', plain,
% 0.62/0.81      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.62/0.81         (~ (r1_tarski @ X14 @ X15)
% 0.62/0.81          | (r1_tarski @ (k4_xboole_0 @ X16 @ X15) @ (k4_xboole_0 @ X16 @ X14)))),
% 0.62/0.81      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.62/0.81  thf('8', plain,
% 0.62/0.81      ((![X0 : $i]:
% 0.62/0.81          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ (k4_xboole_0 @ X0 @ sk_B)))
% 0.62/0.81         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['6', '7'])).
% 0.62/0.81  thf('9', plain,
% 0.62/0.81      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.62/0.81         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.62/0.81      inference('sup+', [status(thm)], ['4', '8'])).
% 0.62/0.81  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('11', plain,
% 0.62/0.81      (![X35 : $i, X36 : $i]:
% 0.62/0.81         (((k3_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))
% 0.62/0.81          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35)))),
% 0.62/0.81      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.62/0.81  thf('12', plain,
% 0.62/0.81      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.62/0.81      inference('sup-', [status(thm)], ['10', '11'])).
% 0.62/0.81  thf('13', plain,
% 0.62/0.81      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.62/0.81         <= (((r1_tarski @ sk_B @ sk_C)))),
% 0.62/0.81      inference('demod', [status(thm)], ['9', '12'])).
% 0.62/0.81  thf('14', plain,
% 0.62/0.81      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.62/0.81           (k3_subset_1 @ sk_A @ sk_B)))
% 0.62/0.81         <= (~
% 0.62/0.81             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.62/0.81               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.62/0.81      inference('split', [status(esa)], ['0'])).
% 0.62/0.81  thf('15', plain,
% 0.62/0.81      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.62/0.81       ~ ((r1_tarski @ sk_B @ sk_C))),
% 0.62/0.81      inference('sup-', [status(thm)], ['13', '14'])).
% 0.62/0.81  thf('16', plain,
% 0.62/0.81      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.62/0.81       ((r1_tarski @ sk_B @ sk_C))),
% 0.62/0.81      inference('split', [status(esa)], ['5'])).
% 0.62/0.81  thf('17', plain,
% 0.62/0.81      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.62/0.81      inference('sup-', [status(thm)], ['2', '3'])).
% 0.62/0.81  thf(t48_xboole_1, axiom,
% 0.62/0.81    (![A:$i,B:$i]:
% 0.62/0.81     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.62/0.81  thf('18', plain,
% 0.62/0.81      (![X20 : $i, X21 : $i]:
% 0.62/0.81         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.62/0.81           = (k3_xboole_0 @ X20 @ X21))),
% 0.62/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.62/0.81  thf('19', plain,
% 0.62/0.81      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C))
% 0.62/0.81         = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.62/0.81      inference('sup+', [status(thm)], ['17', '18'])).
% 0.62/0.81  thf(commutativity_k3_xboole_0, axiom,
% 0.62/0.81    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.62/0.81  thf('20', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.62/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.62/0.81  thf('21', plain,
% 0.62/0.81      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C))
% 0.62/0.81         = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.62/0.81      inference('demod', [status(thm)], ['19', '20'])).
% 0.62/0.81  thf('22', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf(d2_subset_1, axiom,
% 0.62/0.81    (![A:$i,B:$i]:
% 0.62/0.81     ( ( ( v1_xboole_0 @ A ) =>
% 0.62/0.81         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.62/0.81       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.62/0.81         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.62/0.81  thf('23', plain,
% 0.62/0.81      (![X32 : $i, X33 : $i]:
% 0.62/0.81         (~ (m1_subset_1 @ X32 @ X33)
% 0.62/0.81          | (r2_hidden @ X32 @ X33)
% 0.62/0.81          | (v1_xboole_0 @ X33))),
% 0.62/0.81      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.62/0.81  thf('24', plain,
% 0.62/0.81      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.62/0.81        | (r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['22', '23'])).
% 0.62/0.81  thf(fc1_subset_1, axiom,
% 0.62/0.81    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.62/0.81  thf('25', plain, (![X37 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X37))),
% 0.62/0.81      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.62/0.81  thf('26', plain, ((r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.62/0.81      inference('clc', [status(thm)], ['24', '25'])).
% 0.62/0.81  thf(l49_zfmisc_1, axiom,
% 0.62/0.81    (![A:$i,B:$i]:
% 0.62/0.81     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.62/0.81  thf('27', plain,
% 0.62/0.81      (![X29 : $i, X30 : $i]:
% 0.62/0.81         ((r1_tarski @ X29 @ (k3_tarski @ X30)) | ~ (r2_hidden @ X29 @ X30))),
% 0.62/0.81      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.62/0.81  thf('28', plain, ((r1_tarski @ sk_C @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['26', '27'])).
% 0.62/0.81  thf(t99_zfmisc_1, axiom,
% 0.62/0.81    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.62/0.81  thf('29', plain, (![X31 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X31)) = (X31))),
% 0.62/0.81      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.62/0.81  thf('30', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.62/0.81      inference('demod', [status(thm)], ['28', '29'])).
% 0.62/0.81  thf(t36_xboole_1, axiom,
% 0.62/0.81    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.62/0.81  thf('31', plain,
% 0.62/0.81      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 0.62/0.81      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.62/0.81  thf(t1_xboole_1, axiom,
% 0.62/0.81    (![A:$i,B:$i,C:$i]:
% 0.62/0.81     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.62/0.81       ( r1_tarski @ A @ C ) ))).
% 0.62/0.81  thf('32', plain,
% 0.62/0.81      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.62/0.81         (~ (r1_tarski @ X8 @ X9)
% 0.62/0.81          | ~ (r1_tarski @ X9 @ X10)
% 0.62/0.81          | (r1_tarski @ X8 @ X10))),
% 0.62/0.81      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.62/0.81  thf('33', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.81         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.62/0.81      inference('sup-', [status(thm)], ['31', '32'])).
% 0.62/0.81  thf('34', plain,
% 0.62/0.81      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_C @ X0) @ sk_A)),
% 0.62/0.81      inference('sup-', [status(thm)], ['30', '33'])).
% 0.62/0.81  thf(t79_xboole_1, axiom,
% 0.62/0.81    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.62/0.81  thf('35', plain,
% 0.62/0.81      (![X24 : $i, X25 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ X25)),
% 0.62/0.81      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.62/0.81  thf(t69_xboole_1, axiom,
% 0.62/0.81    (![A:$i,B:$i]:
% 0.62/0.81     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.62/0.81       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.62/0.81  thf('36', plain,
% 0.62/0.81      (![X22 : $i, X23 : $i]:
% 0.62/0.81         (~ (r1_xboole_0 @ X22 @ X23)
% 0.62/0.81          | ~ (r1_tarski @ X22 @ X23)
% 0.62/0.81          | (v1_xboole_0 @ X22))),
% 0.62/0.81      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.62/0.81  thf('37', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 0.62/0.81          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.62/0.81      inference('sup-', [status(thm)], ['35', '36'])).
% 0.62/0.81  thf('38', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A))),
% 0.62/0.81      inference('sup-', [status(thm)], ['34', '37'])).
% 0.62/0.81  thf(l13_xboole_0, axiom,
% 0.62/0.81    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.62/0.81  thf('39', plain,
% 0.62/0.81      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.62/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.62/0.81  thf('40', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.62/0.81      inference('sup-', [status(thm)], ['38', '39'])).
% 0.62/0.81  thf('41', plain,
% 0.62/0.81      (![X20 : $i, X21 : $i]:
% 0.62/0.81         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.62/0.81           = (k3_xboole_0 @ X20 @ X21))),
% 0.62/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.62/0.81  thf('42', plain,
% 0.62/0.81      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.62/0.81      inference('sup+', [status(thm)], ['40', '41'])).
% 0.62/0.81  thf(t3_boole, axiom,
% 0.62/0.81    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.62/0.81  thf('43', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.62/0.81      inference('cnf', [status(esa)], [t3_boole])).
% 0.62/0.81  thf('44', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.62/0.81      inference('demod', [status(thm)], ['42', '43'])).
% 0.62/0.81  thf('45', plain,
% 0.62/0.81      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.62/0.81      inference('demod', [status(thm)], ['21', '44'])).
% 0.62/0.81  thf('46', plain,
% 0.62/0.81      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.62/0.81         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.62/0.81               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.62/0.81      inference('split', [status(esa)], ['5'])).
% 0.62/0.81  thf('47', plain,
% 0.62/0.81      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.62/0.81         (~ (r1_tarski @ X14 @ X15)
% 0.62/0.81          | (r1_tarski @ (k4_xboole_0 @ X16 @ X15) @ (k4_xboole_0 @ X16 @ X14)))),
% 0.62/0.81      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.62/0.81  thf('48', plain,
% 0.62/0.81      ((![X0 : $i]:
% 0.62/0.81          (r1_tarski @ (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ 
% 0.62/0.81           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C))))
% 0.62/0.81         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.62/0.81               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.62/0.81      inference('sup-', [status(thm)], ['46', '47'])).
% 0.62/0.81  thf('49', plain,
% 0.62/0.81      (((r1_tarski @ (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) @ sk_C))
% 0.62/0.81         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.62/0.81               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.62/0.81      inference('sup+', [status(thm)], ['45', '48'])).
% 0.62/0.81  thf('50', plain,
% 0.62/0.81      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.62/0.81      inference('sup-', [status(thm)], ['10', '11'])).
% 0.62/0.81  thf('51', plain,
% 0.62/0.81      (![X20 : $i, X21 : $i]:
% 0.62/0.81         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.62/0.81           = (k3_xboole_0 @ X20 @ X21))),
% 0.62/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.62/0.81  thf('52', plain,
% 0.62/0.81      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.62/0.81         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.62/0.81      inference('sup+', [status(thm)], ['50', '51'])).
% 0.62/0.81  thf('53', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.62/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.62/0.81  thf('54', plain,
% 0.62/0.81      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.62/0.81         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.62/0.81      inference('demod', [status(thm)], ['52', '53'])).
% 0.62/0.81  thf('55', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('56', plain,
% 0.62/0.81      (![X32 : $i, X33 : $i]:
% 0.62/0.81         (~ (m1_subset_1 @ X32 @ X33)
% 0.62/0.81          | (r2_hidden @ X32 @ X33)
% 0.62/0.81          | (v1_xboole_0 @ X33))),
% 0.62/0.81      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.62/0.81  thf('57', plain,
% 0.62/0.81      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.62/0.81        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['55', '56'])).
% 0.62/0.81  thf('58', plain, (![X37 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X37))),
% 0.62/0.81      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.62/0.81  thf('59', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.62/0.81      inference('clc', [status(thm)], ['57', '58'])).
% 0.62/0.81  thf('60', plain,
% 0.62/0.81      (![X29 : $i, X30 : $i]:
% 0.62/0.81         ((r1_tarski @ X29 @ (k3_tarski @ X30)) | ~ (r2_hidden @ X29 @ X30))),
% 0.62/0.81      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.62/0.81  thf('61', plain, ((r1_tarski @ sk_B @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['59', '60'])).
% 0.62/0.81  thf('62', plain, (![X31 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X31)) = (X31))),
% 0.62/0.81      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.62/0.81  thf('63', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.62/0.81      inference('demod', [status(thm)], ['61', '62'])).
% 0.62/0.81  thf(t33_xboole_1, axiom,
% 0.62/0.81    (![A:$i,B:$i,C:$i]:
% 0.62/0.81     ( ( r1_tarski @ A @ B ) =>
% 0.62/0.81       ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.62/0.81  thf('64', plain,
% 0.62/0.81      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.62/0.81         (~ (r1_tarski @ X11 @ X12)
% 0.62/0.81          | (r1_tarski @ (k4_xboole_0 @ X11 @ X13) @ (k4_xboole_0 @ X12 @ X13)))),
% 0.62/0.81      inference('cnf', [status(esa)], [t33_xboole_1])).
% 0.62/0.81  thf('65', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (k4_xboole_0 @ sk_A @ X0))),
% 0.62/0.81      inference('sup-', [status(thm)], ['63', '64'])).
% 0.62/0.81  thf(t106_xboole_1, axiom,
% 0.62/0.81    (![A:$i,B:$i,C:$i]:
% 0.62/0.81     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.62/0.81       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.62/0.81  thf('66', plain,
% 0.62/0.81      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.62/0.81         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X7)))),
% 0.62/0.81      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.62/0.81  thf('67', plain,
% 0.62/0.81      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.62/0.81      inference('sup-', [status(thm)], ['65', '66'])).
% 0.62/0.81  thf('68', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 0.62/0.81          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.62/0.81      inference('sup-', [status(thm)], ['35', '36'])).
% 0.62/0.81  thf('69', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A))),
% 0.62/0.81      inference('sup-', [status(thm)], ['67', '68'])).
% 0.62/0.81  thf('70', plain,
% 0.62/0.81      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.62/0.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.62/0.81  thf('71', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.62/0.81      inference('sup-', [status(thm)], ['69', '70'])).
% 0.62/0.81  thf('72', plain,
% 0.62/0.81      (![X20 : $i, X21 : $i]:
% 0.62/0.81         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.62/0.81           = (k3_xboole_0 @ X20 @ X21))),
% 0.62/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.62/0.81  thf('73', plain,
% 0.62/0.81      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.62/0.81      inference('sup+', [status(thm)], ['71', '72'])).
% 0.62/0.81  thf('74', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.62/0.81      inference('cnf', [status(esa)], [t3_boole])).
% 0.62/0.81  thf('75', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.62/0.81      inference('demod', [status(thm)], ['73', '74'])).
% 0.62/0.81  thf('76', plain,
% 0.62/0.81      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.62/0.81      inference('demod', [status(thm)], ['54', '75'])).
% 0.62/0.81  thf('77', plain,
% 0.62/0.81      (((r1_tarski @ sk_B @ sk_C))
% 0.62/0.81         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.62/0.81               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.62/0.81      inference('demod', [status(thm)], ['49', '76'])).
% 0.62/0.81  thf('78', plain,
% 0.62/0.81      ((~ (r1_tarski @ sk_B @ sk_C)) <= (~ ((r1_tarski @ sk_B @ sk_C)))),
% 0.62/0.81      inference('split', [status(esa)], ['0'])).
% 0.62/0.81  thf('79', plain,
% 0.62/0.81      (~
% 0.62/0.81       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.62/0.81       ((r1_tarski @ sk_B @ sk_C))),
% 0.62/0.81      inference('sup-', [status(thm)], ['77', '78'])).
% 0.62/0.81  thf('80', plain, ($false),
% 0.62/0.81      inference('sat_resolution*', [status(thm)], ['1', '15', '16', '79'])).
% 0.62/0.81  
% 0.62/0.81  % SZS output end Refutation
% 0.62/0.81  
% 0.62/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
