%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CieMuyTPio

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:31 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 323 expanded)
%              Number of leaves         :   34 ( 108 expanded)
%              Depth                    :   13
%              Number of atoms          :  731 (2621 expanded)
%              Number of equality atoms :   77 ( 257 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t39_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
        <=> ( B
            = ( k2_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,
    ( ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['2','10'])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('17',plain,(
    ! [X26: $i] :
      ( ( k2_subset_1 @ X26 )
      = X26 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('18',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('19',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('21',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('22',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_B )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('26',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('28',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['16','26','27'])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['14','28'])).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['14','28'])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_tarski @ X17 @ X16 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('42',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('43',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X31 @ ( k3_subset_1 @ X31 @ X30 ) )
        = X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('45',plain,(
    ! [X25: $i] :
      ( ( k1_subset_1 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X32: $i] :
      ( ( k2_subset_1 @ X32 )
      = ( k3_subset_1 @ X32 @ ( k1_subset_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('47',plain,(
    ! [X26: $i] :
      ( ( k2_subset_1 @ X26 )
      = X26 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('48',plain,(
    ! [X32: $i] :
      ( X32
      = ( k3_subset_1 @ X32 @ ( k1_subset_1 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','49'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('51',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X34 @ X33 ) @ ( k3_subset_1 @ X34 @ X35 ) )
      | ( r1_tarski @ X35 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('53',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('54',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X29 ) @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('55',plain,(
    ! [X26: $i] :
      ( ( k2_subset_1 @ X26 )
      = X26 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('56',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53','56'])).

thf('58',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['41','57'])).

thf('59',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('60',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['60','61'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('63',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('64',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['41','57'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('67',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['62','63'])).

thf('68',plain,(
    sk_B = sk_A ),
    inference(demod,[status(thm)],['35','40','64','65','66','67'])).

thf('69',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('70',plain,(
    ! [X26: $i] :
      ( ( k2_subset_1 @ X26 )
      = X26 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('71',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['16','26'])).

thf('73',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['68','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CieMuyTPio
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:41:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.55/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.74  % Solved by: fo/fo7.sh
% 0.55/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.74  % done 1003 iterations in 0.277s
% 0.55/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.74  % SZS output start Refutation
% 0.55/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.55/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.74  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.55/0.74  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.55/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.55/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.74  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.55/0.74  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.74  thf(t39_subset_1, conjecture,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.74       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.55/0.74         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.55/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.74    (~( ![A:$i,B:$i]:
% 0.55/0.74        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.74          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.55/0.74            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.55/0.74    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.55/0.74  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(d5_subset_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.74       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.55/0.74  thf('1', plain,
% 0.55/0.74      (![X27 : $i, X28 : $i]:
% 0.55/0.74         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 0.55/0.74          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.55/0.74      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.55/0.74  thf('2', plain,
% 0.55/0.74      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['0', '1'])).
% 0.55/0.74  thf('3', plain,
% 0.55/0.74      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.55/0.74        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('4', plain,
% 0.55/0.74      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.55/0.74         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.55/0.74      inference('split', [status(esa)], ['3'])).
% 0.55/0.74  thf(t28_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.55/0.74  thf('5', plain,
% 0.55/0.74      (![X9 : $i, X10 : $i]:
% 0.55/0.74         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.55/0.74      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.55/0.74  thf('6', plain,
% 0.55/0.74      ((((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.55/0.74          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.55/0.74         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['4', '5'])).
% 0.55/0.74  thf(commutativity_k3_xboole_0, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.55/0.74  thf('7', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.74  thf('8', plain,
% 0.55/0.74      ((((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.55/0.74          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.55/0.74         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.55/0.74      inference('demod', [status(thm)], ['6', '7'])).
% 0.55/0.74  thf(t100_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.55/0.74  thf('9', plain,
% 0.55/0.74      (![X5 : $i, X6 : $i]:
% 0.55/0.74         ((k4_xboole_0 @ X5 @ X6)
% 0.55/0.74           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.55/0.74  thf('10', plain,
% 0.55/0.74      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.55/0.74          = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.55/0.74         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['8', '9'])).
% 0.55/0.74  thf('11', plain,
% 0.55/0.74      ((((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.55/0.74          = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.55/0.74         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['2', '10'])).
% 0.55/0.74  thf('12', plain,
% 0.55/0.74      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['0', '1'])).
% 0.55/0.74  thf(t98_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.55/0.74  thf('13', plain,
% 0.55/0.74      (![X14 : $i, X15 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ X14 @ X15)
% 0.55/0.74           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.55/0.74  thf('14', plain,
% 0.55/0.74      ((((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.55/0.74          = (k2_xboole_0 @ sk_B @ sk_A)))
% 0.55/0.74         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.55/0.74      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.55/0.74  thf('15', plain,
% 0.55/0.74      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.55/0.74        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('16', plain,
% 0.55/0.74      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.55/0.74       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.55/0.74      inference('split', [status(esa)], ['15'])).
% 0.55/0.74  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.55/0.74  thf('17', plain, (![X26 : $i]: ((k2_subset_1 @ X26) = (X26))),
% 0.55/0.74      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.55/0.74  thf('18', plain,
% 0.55/0.74      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.55/0.74      inference('split', [status(esa)], ['3'])).
% 0.55/0.74  thf('19', plain,
% 0.55/0.74      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.55/0.74      inference('sup+', [status(thm)], ['17', '18'])).
% 0.55/0.74  thf('20', plain,
% 0.55/0.74      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['0', '1'])).
% 0.55/0.74  thf('21', plain,
% 0.55/0.74      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.55/0.74         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.55/0.74      inference('split', [status(esa)], ['15'])).
% 0.55/0.74  thf('22', plain,
% 0.55/0.74      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B))
% 0.55/0.74         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['20', '21'])).
% 0.55/0.74  thf('23', plain,
% 0.55/0.74      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_B))
% 0.55/0.74         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.55/0.74             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['19', '22'])).
% 0.55/0.74  thf('24', plain,
% 0.55/0.74      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.55/0.74      inference('sup+', [status(thm)], ['17', '18'])).
% 0.55/0.74  thf(t36_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.55/0.74  thf('25', plain,
% 0.55/0.74      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.55/0.74      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.55/0.74  thf('26', plain,
% 0.55/0.74      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.55/0.74       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.55/0.74      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.55/0.74  thf('27', plain,
% 0.55/0.74      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.55/0.74       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.55/0.74      inference('split', [status(esa)], ['3'])).
% 0.55/0.74  thf('28', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.55/0.74      inference('sat_resolution*', [status(thm)], ['16', '26', '27'])).
% 0.55/0.74  thf('29', plain,
% 0.55/0.74      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.55/0.74         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.55/0.74      inference('simpl_trail', [status(thm)], ['14', '28'])).
% 0.55/0.74  thf('30', plain,
% 0.55/0.74      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.55/0.74      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.55/0.74  thf(d10_xboole_0, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.74  thf('31', plain,
% 0.55/0.74      (![X2 : $i, X4 : $i]:
% 0.55/0.74         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.55/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.74  thf('32', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.55/0.74          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['30', '31'])).
% 0.55/0.74  thf('33', plain,
% 0.55/0.74      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.55/0.74        | ((sk_B) = (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['29', '32'])).
% 0.55/0.74  thf('34', plain,
% 0.55/0.74      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.55/0.74         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.55/0.74      inference('simpl_trail', [status(thm)], ['14', '28'])).
% 0.55/0.74  thf('35', plain,
% 0.55/0.74      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.55/0.74        | ((sk_B) = (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.55/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.55/0.74  thf(commutativity_k2_tarski, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.55/0.74  thf('36', plain,
% 0.55/0.74      (![X16 : $i, X17 : $i]:
% 0.55/0.74         ((k2_tarski @ X17 @ X16) = (k2_tarski @ X16 @ X17))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.55/0.74  thf(l51_zfmisc_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.55/0.74  thf('37', plain,
% 0.55/0.74      (![X23 : $i, X24 : $i]:
% 0.55/0.74         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 0.55/0.74      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.55/0.74  thf('38', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('sup+', [status(thm)], ['36', '37'])).
% 0.55/0.74  thf('39', plain,
% 0.55/0.74      (![X23 : $i, X24 : $i]:
% 0.55/0.74         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 0.55/0.74      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.55/0.74  thf('40', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('sup+', [status(thm)], ['38', '39'])).
% 0.55/0.74  thf('41', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(t4_subset_1, axiom,
% 0.55/0.74    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.55/0.74  thf('42', plain,
% 0.55/0.74      (![X36 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 0.55/0.74      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.55/0.74  thf(involutiveness_k3_subset_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.74       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.55/0.74  thf('43', plain,
% 0.55/0.74      (![X30 : $i, X31 : $i]:
% 0.55/0.74         (((k3_subset_1 @ X31 @ (k3_subset_1 @ X31 @ X30)) = (X30))
% 0.55/0.74          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 0.55/0.74      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.55/0.74  thf('44', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['42', '43'])).
% 0.55/0.74  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.55/0.74  thf('45', plain, (![X25 : $i]: ((k1_subset_1 @ X25) = (k1_xboole_0))),
% 0.55/0.74      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.55/0.74  thf(t22_subset_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.55/0.74  thf('46', plain,
% 0.55/0.74      (![X32 : $i]:
% 0.55/0.74         ((k2_subset_1 @ X32) = (k3_subset_1 @ X32 @ (k1_subset_1 @ X32)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.55/0.74  thf('47', plain, (![X26 : $i]: ((k2_subset_1 @ X26) = (X26))),
% 0.55/0.74      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.55/0.74  thf('48', plain,
% 0.55/0.74      (![X32 : $i]: ((X32) = (k3_subset_1 @ X32 @ (k1_subset_1 @ X32)))),
% 0.55/0.74      inference('demod', [status(thm)], ['46', '47'])).
% 0.55/0.74  thf('49', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['45', '48'])).
% 0.55/0.74  thf('50', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.55/0.74      inference('demod', [status(thm)], ['44', '49'])).
% 0.55/0.74  thf(t31_subset_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.74       ( ![C:$i]:
% 0.55/0.74         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.74           ( ( r1_tarski @ B @ C ) <=>
% 0.55/0.74             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.55/0.74  thf('51', plain,
% 0.55/0.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.55/0.74          | ~ (r1_tarski @ (k3_subset_1 @ X34 @ X33) @ 
% 0.55/0.74               (k3_subset_1 @ X34 @ X35))
% 0.55/0.74          | (r1_tarski @ X35 @ X33)
% 0.55/0.74          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.55/0.74  thf('52', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ X1 @ X0))
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.55/0.74          | (r1_tarski @ X0 @ X1)
% 0.55/0.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['50', '51'])).
% 0.55/0.74  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.55/0.74  thf('53', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.55/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.55/0.74  thf(dt_k2_subset_1, axiom,
% 0.55/0.74    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.55/0.74  thf('54', plain,
% 0.55/0.74      (![X29 : $i]: (m1_subset_1 @ (k2_subset_1 @ X29) @ (k1_zfmisc_1 @ X29))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.55/0.74  thf('55', plain, (![X26 : $i]: ((k2_subset_1 @ X26) = (X26))),
% 0.55/0.74      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.55/0.74  thf('56', plain, (![X29 : $i]: (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X29))),
% 0.55/0.74      inference('demod', [status(thm)], ['54', '55'])).
% 0.55/0.74  thf('57', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | (r1_tarski @ X0 @ X1))),
% 0.55/0.74      inference('demod', [status(thm)], ['52', '53', '56'])).
% 0.55/0.74  thf('58', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.55/0.74      inference('sup-', [status(thm)], ['41', '57'])).
% 0.55/0.74  thf('59', plain,
% 0.55/0.74      (![X9 : $i, X10 : $i]:
% 0.55/0.74         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.55/0.74      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.55/0.74  thf('60', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['58', '59'])).
% 0.55/0.74  thf('61', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.74  thf('62', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['60', '61'])).
% 0.55/0.74  thf(t22_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.55/0.74  thf('63', plain,
% 0.55/0.74      (![X7 : $i, X8 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 0.55/0.74      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.55/0.74  thf('64', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.55/0.74      inference('sup+', [status(thm)], ['62', '63'])).
% 0.55/0.74  thf('65', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.55/0.74      inference('sup-', [status(thm)], ['41', '57'])).
% 0.55/0.74  thf('66', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('sup+', [status(thm)], ['38', '39'])).
% 0.55/0.74  thf('67', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.55/0.74      inference('sup+', [status(thm)], ['62', '63'])).
% 0.55/0.74  thf('68', plain, (((sk_B) = (sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['35', '40', '64', '65', '66', '67'])).
% 0.55/0.74  thf('69', plain,
% 0.55/0.74      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.55/0.74         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.55/0.74      inference('split', [status(esa)], ['15'])).
% 0.55/0.74  thf('70', plain, (![X26 : $i]: ((k2_subset_1 @ X26) = (X26))),
% 0.55/0.74      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.55/0.74  thf('71', plain,
% 0.55/0.74      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.55/0.74      inference('demod', [status(thm)], ['69', '70'])).
% 0.55/0.74  thf('72', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.55/0.74      inference('sat_resolution*', [status(thm)], ['16', '26'])).
% 0.55/0.74  thf('73', plain, (((sk_B) != (sk_A))),
% 0.55/0.74      inference('simpl_trail', [status(thm)], ['71', '72'])).
% 0.55/0.74  thf('74', plain, ($false),
% 0.55/0.74      inference('simplify_reflect-', [status(thm)], ['68', '73'])).
% 0.55/0.74  
% 0.55/0.74  % SZS output end Refutation
% 0.55/0.74  
% 0.55/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
