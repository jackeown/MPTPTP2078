%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.76OtT7MjdU

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 250 expanded)
%              Number of leaves         :   31 (  88 expanded)
%              Depth                    :   12
%              Number of atoms          :  660 (1756 expanded)
%              Number of equality atoms :   62 ( 169 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('13',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X20: $i] :
      ( ( k1_subset_1 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('16',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('18',plain,(
    ! [X20: $i] :
      ( ( k1_subset_1 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('19',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('23',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('25',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('26',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    sk_B_1
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['17','26'])).

thf('28',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['16','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','28'])).

thf('30',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X24: $i] :
      ( ( k2_subset_1 @ X24 )
      = ( k3_subset_1 @ X24 @ ( k1_subset_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('38',plain,(
    ! [X21: $i] :
      ( ( k2_subset_1 @ X21 )
      = X21 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('39',plain,(
    ! [X20: $i] :
      ( ( k1_subset_1 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('40',plain,(
    ! [X24: $i] :
      ( X24
      = ( k3_subset_1 @ X24 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','41'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k5_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('47',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_tarski @ X18 @ X19 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['30','50'])).

thf('52',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('54',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( r1_tarski @ X25 @ ( k3_subset_1 @ X26 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ ( k3_subset_1 @ X26 @ X25 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('58',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
      | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,(
    ! [X24: $i] :
      ( X24
      = ( k3_subset_1 @ X24 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('62',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('63',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('65',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('67',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k5_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('69',plain,(
    r1_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_tarski @ X18 @ X19 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('71',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( r1_tarski @ sk_B_1 @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['65','66'])).

thf('73',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['19'])).

thf('76',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['19'])).

thf('77',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['17','26','76'])).

thf('78',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['75','77'])).

thf('79',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('80',plain,(
    r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['71','74','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['51','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.76OtT7MjdU
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:22:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 100 iterations in 0.067s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.53  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.22/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.53  thf(d3_tarski, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      (![X8 : $i, X10 : $i]:
% 0.22/0.53         ((r1_tarski @ X8 @ X10) | (r2_hidden @ (sk_C @ X10 @ X8) @ X8))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.53  thf(d1_xboole_0, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.22/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.53  thf(t28_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      (![X15 : $i, X16 : $i]:
% 0.22/0.53         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (~ (v1_xboole_0 @ X1) | ((k3_xboole_0 @ X1 @ X0) = (X1)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.53  thf('5', plain, (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ X17)),
% 0.22/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      (![X15 : $i, X16 : $i]:
% 0.22/0.53         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['4', '9'])).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['4', '9'])).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.53      inference('sup+', [status(thm)], ['10', '11'])).
% 0.22/0.53  thf(t38_subset_1, conjecture,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.53       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.22/0.53         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i,B:$i]:
% 0.22/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.53          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.22/0.53            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.22/0.53        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.22/0.53         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.22/0.53      inference('split', [status(esa)], ['13'])).
% 0.22/0.53  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.53  thf('15', plain, (![X20 : $i]: ((k1_subset_1 @ X20) = (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.22/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) | 
% 0.22/0.53       ~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.22/0.53      inference('split', [status(esa)], ['13'])).
% 0.22/0.53  thf('18', plain, (![X20 : $i]: ((k1_subset_1 @ X20) = (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.53  thf('19', plain,
% 0.22/0.53      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.22/0.53        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.22/0.53         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.22/0.53      inference('split', [status(esa)], ['19'])).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.22/0.53      inference('sup+', [status(thm)], ['18', '20'])).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.22/0.53         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.22/0.53      inference('split', [status(esa)], ['13'])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.22/0.53         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.22/0.53             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.22/0.53      inference('sup+', [status(thm)], ['18', '20'])).
% 0.22/0.53  thf('25', plain, (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ X17)),
% 0.22/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.22/0.53       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.22/0.53      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.22/0.53  thf('27', plain, (~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.22/0.53      inference('sat_resolution*', [status(thm)], ['17', '26'])).
% 0.22/0.53  thf('28', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['16', '27'])).
% 0.22/0.53  thf('29', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((X0) != (k1_xboole_0))
% 0.22/0.53          | ~ (v1_xboole_0 @ X0)
% 0.22/0.53          | ~ (v1_xboole_0 @ sk_B_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['12', '28'])).
% 0.22/0.53  thf('30', plain,
% 0.22/0.53      ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.22/0.53      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.53  thf(t100_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      (![X13 : $i, X14 : $i]:
% 0.22/0.53         ((k4_xboole_0 @ X13 @ X14)
% 0.22/0.53           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.53  thf('33', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['31', '32'])).
% 0.22/0.53  thf(t4_subset_1, axiom,
% 0.22/0.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.53  thf('34', plain,
% 0.22/0.53      (![X28 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 0.22/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.53  thf(d5_subset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.53  thf('35', plain,
% 0.22/0.53      (![X22 : $i, X23 : $i]:
% 0.22/0.53         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 0.22/0.53          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.22/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.53  thf('36', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.53  thf(t22_subset_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.22/0.53  thf('37', plain,
% 0.22/0.53      (![X24 : $i]:
% 0.22/0.53         ((k2_subset_1 @ X24) = (k3_subset_1 @ X24 @ (k1_subset_1 @ X24)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.22/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.53  thf('38', plain, (![X21 : $i]: ((k2_subset_1 @ X21) = (X21))),
% 0.22/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.53  thf('39', plain, (![X20 : $i]: ((k1_subset_1 @ X20) = (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.53  thf('40', plain, (![X24 : $i]: ((X24) = (k3_subset_1 @ X24 @ k1_xboole_0))),
% 0.22/0.53      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.22/0.53  thf('41', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['36', '40'])).
% 0.22/0.53  thf('42', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.53      inference('demod', [status(thm)], ['33', '41'])).
% 0.22/0.53  thf(l97_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.22/0.53  thf('43', plain,
% 0.22/0.53      (![X11 : $i, X12 : $i]:
% 0.22/0.53         (r1_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k5_xboole_0 @ X11 @ X12))),
% 0.22/0.53      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.22/0.53  thf('44', plain,
% 0.22/0.53      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 0.22/0.53      inference('sup+', [status(thm)], ['42', '43'])).
% 0.22/0.53  thf('45', plain,
% 0.22/0.53      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.53  thf('46', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.22/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.22/0.53  thf(t69_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.53       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.22/0.53  thf('47', plain,
% 0.22/0.53      (![X18 : $i, X19 : $i]:
% 0.22/0.53         (~ (r1_xboole_0 @ X18 @ X19)
% 0.22/0.53          | ~ (r1_tarski @ X18 @ X19)
% 0.22/0.53          | (v1_xboole_0 @ X18))),
% 0.22/0.53      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.22/0.53  thf('48', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.53  thf('49', plain, (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ X17)),
% 0.22/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.53  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.53      inference('demod', [status(thm)], ['48', '49'])).
% 0.22/0.53  thf('51', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.22/0.53      inference('simplify_reflect+', [status(thm)], ['30', '50'])).
% 0.22/0.53  thf('52', plain, (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ X17)),
% 0.22/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.53  thf('53', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(t35_subset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.53       ( ![C:$i]:
% 0.22/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.53           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.22/0.53             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.53  thf('54', plain,
% 0.22/0.53      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.22/0.53          | (r1_tarski @ X25 @ (k3_subset_1 @ X26 @ X27))
% 0.22/0.53          | ~ (r1_tarski @ X27 @ (k3_subset_1 @ X26 @ X25))
% 0.22/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.22/0.53  thf('55', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.53          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.22/0.53          | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ X0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.53  thf('56', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('57', plain,
% 0.22/0.53      (![X22 : $i, X23 : $i]:
% 0.22/0.53         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 0.22/0.53          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.22/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.53  thf('58', plain,
% 0.22/0.53      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.22/0.53  thf('59', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.53          | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 0.22/0.53          | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ X0)))),
% 0.22/0.53      inference('demod', [status(thm)], ['55', '58'])).
% 0.22/0.53  thf('60', plain,
% 0.22/0.53      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0))
% 0.22/0.53        | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['52', '59'])).
% 0.22/0.53  thf('61', plain, (![X24 : $i]: ((X24) = (k3_subset_1 @ X24 @ k1_xboole_0))),
% 0.22/0.53      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.22/0.53  thf('62', plain,
% 0.22/0.53      (![X28 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X28))),
% 0.22/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.53  thf('63', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.22/0.53      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.22/0.53  thf('64', plain,
% 0.22/0.53      (![X15 : $i, X16 : $i]:
% 0.22/0.53         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.53  thf('65', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['63', '64'])).
% 0.22/0.53  thf('66', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.53  thf('67', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.22/0.53      inference('demod', [status(thm)], ['65', '66'])).
% 0.22/0.53  thf('68', plain,
% 0.22/0.53      (![X11 : $i, X12 : $i]:
% 0.22/0.53         (r1_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k5_xboole_0 @ X11 @ X12))),
% 0.22/0.53      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.22/0.53  thf('69', plain, ((r1_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_A @ sk_B_1))),
% 0.22/0.53      inference('sup+', [status(thm)], ['67', '68'])).
% 0.22/0.53  thf('70', plain,
% 0.22/0.53      (![X18 : $i, X19 : $i]:
% 0.22/0.53         (~ (r1_xboole_0 @ X18 @ X19)
% 0.22/0.53          | ~ (r1_tarski @ X18 @ X19)
% 0.22/0.53          | (v1_xboole_0 @ X18))),
% 0.22/0.53      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.22/0.53  thf('71', plain,
% 0.22/0.53      (((v1_xboole_0 @ sk_B_1)
% 0.22/0.53        | ~ (r1_tarski @ sk_B_1 @ (k5_xboole_0 @ sk_A @ sk_B_1)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['69', '70'])).
% 0.22/0.53  thf('72', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.22/0.53      inference('demod', [status(thm)], ['65', '66'])).
% 0.22/0.53  thf('73', plain,
% 0.22/0.53      (![X13 : $i, X14 : $i]:
% 0.22/0.53         ((k4_xboole_0 @ X13 @ X14)
% 0.22/0.53           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.53  thf('74', plain,
% 0.22/0.53      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 0.22/0.53      inference('sup+', [status(thm)], ['72', '73'])).
% 0.22/0.53  thf('75', plain,
% 0.22/0.53      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.22/0.53         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.22/0.53      inference('split', [status(esa)], ['19'])).
% 0.22/0.53  thf('76', plain,
% 0.22/0.53      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.22/0.53       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.22/0.53      inference('split', [status(esa)], ['19'])).
% 0.22/0.53  thf('77', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.22/0.53      inference('sat_resolution*', [status(thm)], ['17', '26', '76'])).
% 0.22/0.53  thf('78', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['75', '77'])).
% 0.22/0.53  thf('79', plain,
% 0.22/0.53      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.22/0.53  thf('80', plain, ((r1_tarski @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.22/0.53      inference('demod', [status(thm)], ['78', '79'])).
% 0.22/0.53  thf('81', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.22/0.53      inference('demod', [status(thm)], ['71', '74', '80'])).
% 0.22/0.53  thf('82', plain, ($false), inference('demod', [status(thm)], ['51', '81'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
