%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bgaz8rEstI

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:11 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 202 expanded)
%              Number of leaves         :   39 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :  923 (1913 expanded)
%              Number of equality atoms :   82 ( 171 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(t12_tops_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
          = ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
            = ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('2',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('4',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('6',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) )
    = ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('9',plain,
    ( ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) )
    = ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X33: $i,X35: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( r1_tarski @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('17',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t33_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
            = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k3_subset_1 @ X20 @ ( k7_subset_1 @ X20 @ X21 @ X19 ) )
        = ( k4_subset_1 @ X20 @ ( k3_subset_1 @ X20 @ X21 ) @ X19 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( ( k3_subset_1 @ sk_A @ ( k7_subset_1 @ sk_A @ X0 @ ( k8_setfam_1 @ sk_A @ sk_B ) ) )
        = ( k4_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_A @ ( k7_subset_1 @ sk_A @ sk_A @ ( k8_setfam_1 @ sk_A @ sk_B ) ) )
    = ( k4_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_A ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
          = ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X36 = k1_xboole_0 )
      | ( ( k5_setfam_1 @ X37 @ ( k7_setfam_1 @ X37 @ X36 ) )
        = ( k7_subset_1 @ X37 @ ( k2_subset_1 @ X37 ) @ ( k6_setfam_1 @ X37 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[t48_setfam_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('29',plain,(
    ! [X10: $i] :
      ( ( k1_subset_1 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X18: $i] :
      ( ( k2_subset_1 @ X18 )
      = ( k3_subset_1 @ X18 @ ( k1_subset_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','32'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X36 = k1_xboole_0 )
      | ( ( k5_setfam_1 @ X37 @ ( k7_setfam_1 @ X37 @ X36 ) )
        = ( k7_subset_1 @ X37 @ X37 @ ( k6_setfam_1 @ X37 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X37 ) ) ) ) ),
    inference(demod,[status(thm)],['22','35'])).

thf('37',plain,
    ( ( ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      = ( k7_subset_1 @ sk_A @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( ( B != k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = ( k6_setfam_1 @ A @ B ) ) )
        & ( ( B = k1_xboole_0 )
         => ( ( k8_setfam_1 @ A @ B )
            = A ) ) ) ) )).

thf('39',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( ( k8_setfam_1 @ X24 @ X23 )
        = ( k6_setfam_1 @ X24 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[d10_setfam_1])).

thf('40',plain,
    ( ( ( k8_setfam_1 @ sk_A @ sk_B )
      = ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k8_setfam_1 @ sk_A @ sk_B )
    = ( k6_setfam_1 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      = ( k7_subset_1 @ sk_A @ sk_A @ ( k8_setfam_1 @ sk_A @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = ( k7_subset_1 @ sk_A @ sk_A @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('47',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k2_subset_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('54',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('55',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ X1 )
        = ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('57',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('58',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ X1 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,
    ( ( k4_subset_1 @ sk_A @ k1_xboole_0 @ ( k8_setfam_1 @ sk_A @ sk_B ) )
    = ( k8_setfam_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['53','60'])).

thf('62',plain,
    ( ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
    = ( k8_setfam_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['20','45','52','61'])).

thf('63',plain,
    ( ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('64',plain,
    ( ( k8_setfam_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k3_subset_1 @ sk_A @ ( k8_setfam_1 @ sk_A @ sk_B ) )
    = ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','64'])).

thf('66',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('67',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('68',plain,
    ( ( k3_subset_1 @ sk_A @ ( k8_setfam_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k8_setfam_1 @ sk_A @ sk_B ) )
    = ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,(
    ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k3_subset_1 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k8_setfam_1 @ sk_A @ sk_B )
    = ( k6_setfam_1 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('72',plain,(
    ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k3_subset_1 @ sk_A @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k3_subset_1 @ sk_A @ ( k8_setfam_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('74',plain,(
    ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k4_xboole_0 @ sk_A @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bgaz8rEstI
% 0.16/0.37  % Computer   : n011.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 20:06:42 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.76/0.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.97  % Solved by: fo/fo7.sh
% 0.76/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.97  % done 1540 iterations in 0.486s
% 0.76/0.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.97  % SZS output start Refutation
% 0.76/0.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.76/0.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.76/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.97  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.76/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.97  thf(k8_setfam_1_type, type, k8_setfam_1: $i > $i > $i).
% 0.76/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.76/0.97  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.76/0.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.97  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.76/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.97  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.76/0.97  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.76/0.97  thf(t12_tops_2, conjecture,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.76/0.97       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.76/0.97         ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.76/0.97           ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ))).
% 0.76/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.97    (~( ![A:$i,B:$i]:
% 0.76/0.97        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.76/0.97          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.76/0.97            ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.76/0.97              ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )),
% 0.76/0.97    inference('cnf.neg', [status(esa)], [t12_tops_2])).
% 0.76/0.97  thf('0', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(dt_k7_setfam_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.76/0.97       ( m1_subset_1 @
% 0.76/0.97         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.76/0.97  thf('1', plain,
% 0.76/0.97      (![X27 : $i, X28 : $i]:
% 0.76/0.97         ((m1_subset_1 @ (k7_setfam_1 @ X27 @ X28) @ 
% 0.76/0.97           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X27)))
% 0.76/0.97          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X27))))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.76/0.97  thf('2', plain,
% 0.76/0.97      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.76/0.97        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['0', '1'])).
% 0.76/0.97  thf(dt_k5_setfam_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.76/0.97       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.76/0.97  thf('3', plain,
% 0.76/0.97      (![X25 : $i, X26 : $i]:
% 0.76/0.97         ((m1_subset_1 @ (k5_setfam_1 @ X25 @ X26) @ (k1_zfmisc_1 @ X25))
% 0.76/0.97          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X25))))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.76/0.97  thf('4', plain,
% 0.76/0.97      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) @ 
% 0.76/0.97        (k1_zfmisc_1 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf(involutiveness_k3_subset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.76/0.97  thf('5', plain,
% 0.76/0.97      (![X13 : $i, X14 : $i]:
% 0.76/0.97         (((k3_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X13)) = (X13))
% 0.76/0.97          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.76/0.97      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.76/0.97  thf('6', plain,
% 0.76/0.97      (((k3_subset_1 @ sk_A @ 
% 0.76/0.97         (k3_subset_1 @ sk_A @ 
% 0.76/0.97          (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))
% 0.76/0.97         = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['4', '5'])).
% 0.76/0.97  thf('7', plain,
% 0.76/0.97      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) @ 
% 0.76/0.97        (k1_zfmisc_1 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf(d5_subset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.76/0.97  thf('8', plain,
% 0.76/0.97      (![X11 : $i, X12 : $i]:
% 0.76/0.97         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.76/0.97          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.76/0.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.76/0.97  thf('9', plain,
% 0.76/0.97      (((k3_subset_1 @ sk_A @ 
% 0.76/0.97         (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.76/0.97         = (k4_xboole_0 @ sk_A @ 
% 0.76/0.97            (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['7', '8'])).
% 0.76/0.97  thf('10', plain,
% 0.76/0.97      (((k3_subset_1 @ sk_A @ 
% 0.76/0.97         (k4_xboole_0 @ sk_A @ 
% 0.76/0.97          (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))
% 0.76/0.97         = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('demod', [status(thm)], ['6', '9'])).
% 0.76/0.97  thf(d10_xboole_0, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/0.97  thf('11', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.76/0.97      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.97  thf('12', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.76/0.97      inference('simplify', [status(thm)], ['11'])).
% 0.76/0.97  thf(t3_subset, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.97  thf('13', plain,
% 0.76/0.97      (![X33 : $i, X35 : $i]:
% 0.76/0.97         ((m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X35)) | ~ (r1_tarski @ X33 @ X35))),
% 0.76/0.97      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.97  thf('14', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['12', '13'])).
% 0.76/0.97  thf('15', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(dt_k8_setfam_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.76/0.97       ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.76/0.97  thf('16', plain,
% 0.76/0.97      (![X29 : $i, X30 : $i]:
% 0.76/0.97         ((m1_subset_1 @ (k8_setfam_1 @ X29 @ X30) @ (k1_zfmisc_1 @ X29))
% 0.76/0.97          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X29))))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k8_setfam_1])).
% 0.76/0.97  thf('17', plain,
% 0.76/0.97      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['15', '16'])).
% 0.76/0.97  thf(t33_subset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97       ( ![C:$i]:
% 0.76/0.97         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97           ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 0.76/0.97             ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.76/0.97  thf('18', plain,
% 0.76/0.97      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.76/0.97          | ((k3_subset_1 @ X20 @ (k7_subset_1 @ X20 @ X21 @ X19))
% 0.76/0.97              = (k4_subset_1 @ X20 @ (k3_subset_1 @ X20 @ X21) @ X19))
% 0.76/0.97          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t33_subset_1])).
% 0.76/0.97  thf('19', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.76/0.97          | ((k3_subset_1 @ sk_A @ 
% 0.76/0.97              (k7_subset_1 @ sk_A @ X0 @ (k8_setfam_1 @ sk_A @ sk_B)))
% 0.76/0.97              = (k4_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.76/0.97                 (k8_setfam_1 @ sk_A @ sk_B))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['17', '18'])).
% 0.76/0.97  thf('20', plain,
% 0.76/0.97      (((k3_subset_1 @ sk_A @ 
% 0.76/0.97         (k7_subset_1 @ sk_A @ sk_A @ (k8_setfam_1 @ sk_A @ sk_B)))
% 0.76/0.97         = (k4_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_A) @ 
% 0.76/0.97            (k8_setfam_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['14', '19'])).
% 0.76/0.97  thf('21', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(t48_setfam_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.76/0.97       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.76/0.97         ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.76/0.97           ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k6_setfam_1 @ A @ B ) ) ) ) ))).
% 0.76/0.97  thf('22', plain,
% 0.76/0.97      (![X36 : $i, X37 : $i]:
% 0.76/0.97         (((X36) = (k1_xboole_0))
% 0.76/0.97          | ((k5_setfam_1 @ X37 @ (k7_setfam_1 @ X37 @ X36))
% 0.76/0.97              = (k7_subset_1 @ X37 @ (k2_subset_1 @ X37) @ 
% 0.76/0.97                 (k6_setfam_1 @ X37 @ X36)))
% 0.76/0.97          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X37))))),
% 0.76/0.97      inference('cnf', [status(esa)], [t48_setfam_1])).
% 0.76/0.97  thf(t2_boole, axiom,
% 0.76/0.97    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.76/0.97  thf('23', plain,
% 0.76/0.97      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.97      inference('cnf', [status(esa)], [t2_boole])).
% 0.76/0.97  thf(t100_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.76/0.97  thf('24', plain,
% 0.76/0.97      (![X3 : $i, X4 : $i]:
% 0.76/0.97         ((k4_xboole_0 @ X3 @ X4)
% 0.76/0.97           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.76/0.97  thf('25', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['23', '24'])).
% 0.76/0.97  thf(t4_subset_1, axiom,
% 0.76/0.97    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.76/0.97  thf('26', plain,
% 0.76/0.97      (![X22 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X22))),
% 0.76/0.97      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.76/0.97  thf('27', plain,
% 0.76/0.97      (![X11 : $i, X12 : $i]:
% 0.76/0.97         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.76/0.97          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.76/0.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.76/0.97  thf('28', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['26', '27'])).
% 0.76/0.97  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.76/0.97  thf('29', plain, (![X10 : $i]: ((k1_subset_1 @ X10) = (k1_xboole_0))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.76/0.97  thf(t22_subset_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.76/0.97  thf('30', plain,
% 0.76/0.97      (![X18 : $i]:
% 0.76/0.97         ((k2_subset_1 @ X18) = (k3_subset_1 @ X18 @ (k1_subset_1 @ X18)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.76/0.97  thf('31', plain,
% 0.76/0.97      (![X0 : $i]: ((k2_subset_1 @ X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['29', '30'])).
% 0.76/0.97  thf('32', plain,
% 0.76/0.97      (![X0 : $i]: ((k2_subset_1 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['28', '31'])).
% 0.76/0.97  thf('33', plain,
% 0.76/0.97      (![X0 : $i]: ((k2_subset_1 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.76/0.97      inference('demod', [status(thm)], ['25', '32'])).
% 0.76/0.97  thf(t5_boole, axiom,
% 0.76/0.97    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.76/0.97  thf('34', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.76/0.97      inference('cnf', [status(esa)], [t5_boole])).
% 0.76/0.97  thf('35', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['33', '34'])).
% 0.76/0.97  thf('36', plain,
% 0.76/0.97      (![X36 : $i, X37 : $i]:
% 0.76/0.97         (((X36) = (k1_xboole_0))
% 0.76/0.97          | ((k5_setfam_1 @ X37 @ (k7_setfam_1 @ X37 @ X36))
% 0.76/0.97              = (k7_subset_1 @ X37 @ X37 @ (k6_setfam_1 @ X37 @ X36)))
% 0.76/0.97          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X37))))),
% 0.76/0.97      inference('demod', [status(thm)], ['22', '35'])).
% 0.76/0.97  thf('37', plain,
% 0.76/0.97      ((((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.76/0.97          = (k7_subset_1 @ sk_A @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B)))
% 0.76/0.97        | ((sk_B) = (k1_xboole_0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['21', '36'])).
% 0.76/0.97  thf('38', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(d10_setfam_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.76/0.97       ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.76/0.97           ( ( k8_setfam_1 @ A @ B ) = ( k6_setfam_1 @ A @ B ) ) ) & 
% 0.76/0.97         ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( k8_setfam_1 @ A @ B ) = ( A ) ) ) ) ))).
% 0.76/0.97  thf('39', plain,
% 0.76/0.97      (![X23 : $i, X24 : $i]:
% 0.76/0.97         (((X23) = (k1_xboole_0))
% 0.76/0.97          | ((k8_setfam_1 @ X24 @ X23) = (k6_setfam_1 @ X24 @ X23))
% 0.76/0.97          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24))))),
% 0.76/0.97      inference('cnf', [status(esa)], [d10_setfam_1])).
% 0.76/0.97  thf('40', plain,
% 0.76/0.97      ((((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))
% 0.76/0.97        | ((sk_B) = (k1_xboole_0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['38', '39'])).
% 0.76/0.97  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('42', plain,
% 0.76/0.97      (((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))),
% 0.76/0.97      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.76/0.97  thf('43', plain,
% 0.76/0.97      ((((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.76/0.97          = (k7_subset_1 @ sk_A @ sk_A @ (k8_setfam_1 @ sk_A @ sk_B)))
% 0.76/0.97        | ((sk_B) = (k1_xboole_0)))),
% 0.76/0.97      inference('demod', [status(thm)], ['37', '42'])).
% 0.76/0.97  thf('44', plain, (((sk_B) != (k1_xboole_0))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('45', plain,
% 0.76/0.97      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.76/0.97         = (k7_subset_1 @ sk_A @ sk_A @ (k8_setfam_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.76/0.97  thf('46', plain,
% 0.76/0.97      (![X22 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X22))),
% 0.76/0.97      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.76/0.97  thf('47', plain,
% 0.76/0.97      (![X13 : $i, X14 : $i]:
% 0.76/0.97         (((k3_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X13)) = (X13))
% 0.76/0.97          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.76/0.97      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.76/0.97  thf('48', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['46', '47'])).
% 0.76/0.97  thf('49', plain,
% 0.76/0.97      (![X0 : $i]: ((k2_subset_1 @ X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['29', '30'])).
% 0.76/0.97  thf('50', plain,
% 0.76/0.97      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k2_subset_1 @ X0)) = (k1_xboole_0))),
% 0.76/0.97      inference('demod', [status(thm)], ['48', '49'])).
% 0.76/0.97  thf('51', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['33', '34'])).
% 0.76/0.97  thf('52', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.76/0.97      inference('demod', [status(thm)], ['50', '51'])).
% 0.76/0.97  thf('53', plain,
% 0.76/0.97      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['15', '16'])).
% 0.76/0.97  thf('54', plain,
% 0.76/0.97      (![X22 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X22))),
% 0.76/0.97      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.76/0.97  thf(redefinition_k4_subset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.76/0.97         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.76/0.97       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.76/0.97  thf('55', plain,
% 0.76/0.97      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.76/0.97          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 0.76/0.97          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 0.76/0.97      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.76/0.97  thf('56', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((k4_subset_1 @ X0 @ k1_xboole_0 @ X1)
% 0.76/0.97            = (k2_xboole_0 @ k1_xboole_0 @ X1))
% 0.76/0.97          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['54', '55'])).
% 0.76/0.97  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.76/0.97  thf('57', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.76/0.97      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.76/0.97  thf(t12_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.76/0.97  thf('58', plain,
% 0.76/0.97      (![X5 : $i, X6 : $i]:
% 0.76/0.97         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.76/0.97      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.97  thf('59', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['57', '58'])).
% 0.76/0.97  thf('60', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((k4_subset_1 @ X0 @ k1_xboole_0 @ X1) = (X1))
% 0.76/0.97          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.76/0.97      inference('demod', [status(thm)], ['56', '59'])).
% 0.76/0.97  thf('61', plain,
% 0.76/0.97      (((k4_subset_1 @ sk_A @ k1_xboole_0 @ (k8_setfam_1 @ sk_A @ sk_B))
% 0.76/0.97         = (k8_setfam_1 @ sk_A @ sk_B))),
% 0.76/0.97      inference('sup-', [status(thm)], ['53', '60'])).
% 0.76/0.97  thf('62', plain,
% 0.76/0.97      (((k3_subset_1 @ sk_A @ 
% 0.76/0.97         (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.76/0.97         = (k8_setfam_1 @ sk_A @ sk_B))),
% 0.76/0.97      inference('demod', [status(thm)], ['20', '45', '52', '61'])).
% 0.76/0.97  thf('63', plain,
% 0.76/0.97      (((k3_subset_1 @ sk_A @ 
% 0.76/0.97         (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.76/0.97         = (k4_xboole_0 @ sk_A @ 
% 0.76/0.97            (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['7', '8'])).
% 0.76/0.97  thf('64', plain,
% 0.76/0.97      (((k8_setfam_1 @ sk_A @ sk_B)
% 0.76/0.97         = (k4_xboole_0 @ sk_A @ 
% 0.76/0.97            (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.76/0.97      inference('sup+', [status(thm)], ['62', '63'])).
% 0.76/0.97  thf('65', plain,
% 0.76/0.97      (((k3_subset_1 @ sk_A @ (k8_setfam_1 @ sk_A @ sk_B))
% 0.76/0.97         = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('demod', [status(thm)], ['10', '64'])).
% 0.76/0.97  thf('66', plain,
% 0.76/0.97      ((m1_subset_1 @ (k8_setfam_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['15', '16'])).
% 0.76/0.97  thf('67', plain,
% 0.76/0.97      (![X11 : $i, X12 : $i]:
% 0.76/0.97         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.76/0.97          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.76/0.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.76/0.97  thf('68', plain,
% 0.76/0.97      (((k3_subset_1 @ sk_A @ (k8_setfam_1 @ sk_A @ sk_B))
% 0.76/0.97         = (k4_xboole_0 @ sk_A @ (k8_setfam_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['66', '67'])).
% 0.76/0.97  thf('69', plain,
% 0.76/0.97      (((k4_xboole_0 @ sk_A @ (k8_setfam_1 @ sk_A @ sk_B))
% 0.76/0.97         = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('demod', [status(thm)], ['65', '68'])).
% 0.76/0.97  thf('70', plain,
% 0.76/0.97      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.76/0.97         != (k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('71', plain,
% 0.76/0.97      (((k8_setfam_1 @ sk_A @ sk_B) = (k6_setfam_1 @ sk_A @ sk_B))),
% 0.76/0.97      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.76/0.97  thf('72', plain,
% 0.76/0.97      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.76/0.97         != (k3_subset_1 @ sk_A @ (k8_setfam_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('demod', [status(thm)], ['70', '71'])).
% 0.76/0.97  thf('73', plain,
% 0.76/0.97      (((k3_subset_1 @ sk_A @ (k8_setfam_1 @ sk_A @ sk_B))
% 0.76/0.97         = (k4_xboole_0 @ sk_A @ (k8_setfam_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['66', '67'])).
% 0.76/0.97  thf('74', plain,
% 0.76/0.97      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.76/0.97         != (k4_xboole_0 @ sk_A @ (k8_setfam_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('demod', [status(thm)], ['72', '73'])).
% 0.76/0.97  thf('75', plain, ($false),
% 0.76/0.97      inference('simplify_reflect-', [status(thm)], ['69', '74'])).
% 0.76/0.97  
% 0.76/0.97  % SZS output end Refutation
% 0.76/0.97  
% 0.76/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
