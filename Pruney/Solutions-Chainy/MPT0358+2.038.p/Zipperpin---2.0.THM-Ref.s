%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.g7zWb1N2Uu

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:27 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 250 expanded)
%              Number of leaves         :   24 (  77 expanded)
%              Depth                    :   15
%              Number of atoms          :  652 (2010 expanded)
%              Number of equality atoms :   61 ( 183 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('10',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X28 @ ( k3_subset_1 @ X28 @ X27 ) )
        = X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('13',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['15'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_xboole_0 @ X10 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('18',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ( X15
       != ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ( m1_subset_1 @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('30',plain,(
    ! [X26: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X28 @ ( k3_subset_1 @ X28 @ X27 ) )
        = X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('35',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['33','40'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('42',plain,(
    ! [X21: $i] :
      ( ( k1_subset_1 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('43',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('44',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['21'])).

thf('46',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('48',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ X19 )
      | ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('54',plain,
    ( ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X26: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('56',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( r1_tarski @ X16 @ X14 )
      | ( X15
       != ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('58',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','59'])).

thf('61',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('62',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['22','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['20','62'])).

thf('64',plain,(
    r1_xboole_0 @ sk_B @ sk_B ),
    inference('sup+',[status(thm)],['14','63'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('65',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X9 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('66',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X21: $i] :
      ( ( k1_subset_1 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('68',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('69',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    sk_B
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['22','60'])).

thf('71',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['66','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.g7zWb1N2Uu
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:21:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 516 iterations in 0.147s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.42/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.61  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.42/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.61  thf(t38_subset_1, conjecture,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.42/0.61         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.61    (~( ![A:$i,B:$i]:
% 0.42/0.61        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.42/0.61            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.42/0.61  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(dt_k3_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.42/0.61  thf('1', plain,
% 0.42/0.61      (![X24 : $i, X25 : $i]:
% 0.42/0.61         ((m1_subset_1 @ (k3_subset_1 @ X24 @ X25) @ (k1_zfmisc_1 @ X24))
% 0.42/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.42/0.61  thf('2', plain,
% 0.42/0.61      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.42/0.61  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(d5_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.42/0.61  thf('4', plain,
% 0.42/0.61      (![X22 : $i, X23 : $i]:
% 0.42/0.61         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 0.42/0.61          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.42/0.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.42/0.61  thf('5', plain,
% 0.42/0.61      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.42/0.61  thf('6', plain,
% 0.42/0.61      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['2', '5'])).
% 0.42/0.61  thf('7', plain,
% 0.42/0.61      (![X22 : $i, X23 : $i]:
% 0.42/0.61         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 0.42/0.61          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.42/0.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.42/0.61         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.42/0.61  thf('9', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(involutiveness_k3_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.42/0.61  thf('10', plain,
% 0.42/0.61      (![X27 : $i, X28 : $i]:
% 0.42/0.61         (((k3_subset_1 @ X28 @ (k3_subset_1 @ X28 @ X27)) = (X27))
% 0.42/0.61          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28)))),
% 0.42/0.61      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.42/0.61  thf('11', plain,
% 0.42/0.61      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.42/0.61  thf('12', plain,
% 0.42/0.61      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.42/0.61      inference('demod', [status(thm)], ['11', '12'])).
% 0.42/0.61  thf('14', plain,
% 0.42/0.61      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.42/0.61      inference('sup+', [status(thm)], ['8', '13'])).
% 0.42/0.61  thf('15', plain,
% 0.42/0.61      ((((sk_B) = (k1_subset_1 @ sk_A))
% 0.42/0.61        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('16', plain,
% 0.42/0.61      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.42/0.61         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.42/0.61      inference('split', [status(esa)], ['15'])).
% 0.42/0.61  thf(t85_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.42/0.61  thf('17', plain,
% 0.42/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.42/0.61         (~ (r1_tarski @ X10 @ X11)
% 0.42/0.61          | (r1_xboole_0 @ X10 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.42/0.61  thf('18', plain,
% 0.42/0.61      ((![X0 : $i]:
% 0.42/0.61          (r1_xboole_0 @ sk_B @ 
% 0.42/0.61           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.42/0.61         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.61  thf('19', plain,
% 0.42/0.61      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.42/0.61  thf('20', plain,
% 0.42/0.61      ((![X0 : $i]:
% 0.42/0.61          (r1_xboole_0 @ sk_B @ 
% 0.42/0.61           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))))
% 0.42/0.61         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.42/0.61      inference('demod', [status(thm)], ['18', '19'])).
% 0.42/0.61  thf('21', plain,
% 0.42/0.61      ((((sk_B) != (k1_subset_1 @ sk_A))
% 0.42/0.61        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('22', plain,
% 0.42/0.61      (~ (((sk_B) = (k1_subset_1 @ sk_A))) | 
% 0.42/0.61       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.42/0.61      inference('split', [status(esa)], ['21'])).
% 0.42/0.61  thf(d10_xboole_0, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.61  thf('23', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.42/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.42/0.61  thf('24', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.42/0.61      inference('simplify', [status(thm)], ['23'])).
% 0.42/0.61  thf(d1_zfmisc_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.42/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.42/0.61  thf('25', plain,
% 0.42/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.42/0.61         (~ (r1_tarski @ X13 @ X14)
% 0.42/0.61          | (r2_hidden @ X13 @ X15)
% 0.42/0.61          | ((X15) != (k1_zfmisc_1 @ X14)))),
% 0.42/0.61      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.42/0.61  thf('26', plain,
% 0.42/0.61      (![X13 : $i, X14 : $i]:
% 0.42/0.61         ((r2_hidden @ X13 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X13 @ X14))),
% 0.42/0.61      inference('simplify', [status(thm)], ['25'])).
% 0.42/0.61  thf('27', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['24', '26'])).
% 0.42/0.61  thf(d2_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( v1_xboole_0 @ A ) =>
% 0.42/0.61         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.42/0.61       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.42/0.61         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.42/0.61  thf('28', plain,
% 0.42/0.61      (![X18 : $i, X19 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X18 @ X19)
% 0.42/0.61          | (m1_subset_1 @ X18 @ X19)
% 0.42/0.61          | (v1_xboole_0 @ X19))),
% 0.42/0.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.42/0.61  thf('29', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.42/0.61  thf(fc1_subset_1, axiom,
% 0.42/0.61    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.42/0.61  thf('30', plain, (![X26 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X26))),
% 0.42/0.61      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.42/0.61  thf('31', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.42/0.61      inference('clc', [status(thm)], ['29', '30'])).
% 0.42/0.61  thf('32', plain,
% 0.42/0.61      (![X27 : $i, X28 : $i]:
% 0.42/0.61         (((k3_subset_1 @ X28 @ (k3_subset_1 @ X28 @ X27)) = (X27))
% 0.42/0.61          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28)))),
% 0.42/0.61      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.42/0.61  thf('33', plain,
% 0.42/0.61      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.42/0.61  thf('34', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.42/0.61      inference('clc', [status(thm)], ['29', '30'])).
% 0.42/0.61  thf('35', plain,
% 0.42/0.61      (![X22 : $i, X23 : $i]:
% 0.42/0.61         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 0.42/0.61          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.42/0.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.42/0.61  thf('36', plain,
% 0.42/0.61      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.42/0.61  thf('37', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.42/0.61      inference('simplify', [status(thm)], ['23'])).
% 0.42/0.61  thf(l32_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.61  thf('38', plain,
% 0.42/0.61      (![X3 : $i, X5 : $i]:
% 0.42/0.61         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.42/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.42/0.61  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.42/0.61  thf('40', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.61      inference('demod', [status(thm)], ['36', '39'])).
% 0.42/0.61  thf('41', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['33', '40'])).
% 0.42/0.61  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.42/0.61  thf('42', plain, (![X21 : $i]: ((k1_subset_1 @ X21) = (k1_xboole_0))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.42/0.61  thf('43', plain,
% 0.42/0.61      ((((sk_B) = (k1_subset_1 @ sk_A))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.42/0.61      inference('split', [status(esa)], ['15'])).
% 0.42/0.61  thf('44', plain,
% 0.42/0.61      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.42/0.61      inference('sup+', [status(thm)], ['42', '43'])).
% 0.42/0.61  thf('45', plain,
% 0.42/0.61      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.42/0.61         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.42/0.61      inference('split', [status(esa)], ['21'])).
% 0.42/0.61  thf('46', plain,
% 0.42/0.61      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.42/0.61         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.42/0.61             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.42/0.61  thf('47', plain,
% 0.42/0.61      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.42/0.61      inference('sup+', [status(thm)], ['42', '43'])).
% 0.42/0.61  thf('48', plain,
% 0.42/0.61      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.42/0.61         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.42/0.61             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.42/0.61      inference('demod', [status(thm)], ['46', '47'])).
% 0.42/0.61  thf('49', plain,
% 0.42/0.61      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.42/0.61         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.42/0.61             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['41', '48'])).
% 0.42/0.61  thf('50', plain,
% 0.42/0.61      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.42/0.61      inference('sup+', [status(thm)], ['42', '43'])).
% 0.42/0.61  thf('51', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('52', plain,
% 0.42/0.61      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))
% 0.42/0.61         <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.42/0.61      inference('sup+', [status(thm)], ['50', '51'])).
% 0.42/0.61  thf('53', plain,
% 0.42/0.61      (![X18 : $i, X19 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X18 @ X19)
% 0.42/0.61          | (r2_hidden @ X18 @ X19)
% 0.42/0.61          | (v1_xboole_0 @ X19))),
% 0.42/0.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.42/0.61  thf('54', plain,
% 0.42/0.61      ((((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.61         | (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A))))
% 0.42/0.61         <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['52', '53'])).
% 0.42/0.61  thf('55', plain, (![X26 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X26))),
% 0.42/0.61      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.42/0.61  thf('56', plain,
% 0.42/0.61      (((r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))
% 0.42/0.61         <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.42/0.61      inference('clc', [status(thm)], ['54', '55'])).
% 0.42/0.61  thf('57', plain,
% 0.42/0.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X16 @ X15)
% 0.42/0.61          | (r1_tarski @ X16 @ X14)
% 0.42/0.61          | ((X15) != (k1_zfmisc_1 @ X14)))),
% 0.42/0.61      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.42/0.61  thf('58', plain,
% 0.42/0.61      (![X14 : $i, X16 : $i]:
% 0.42/0.61         ((r1_tarski @ X16 @ X14) | ~ (r2_hidden @ X16 @ (k1_zfmisc_1 @ X14)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['57'])).
% 0.42/0.61  thf('59', plain,
% 0.42/0.61      (((r1_tarski @ k1_xboole_0 @ sk_A))
% 0.42/0.61         <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['56', '58'])).
% 0.42/0.61  thf('60', plain,
% 0.42/0.61      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.42/0.61       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.42/0.61      inference('demod', [status(thm)], ['49', '59'])).
% 0.42/0.61  thf('61', plain,
% 0.42/0.61      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.42/0.61       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.42/0.61      inference('split', [status(esa)], ['15'])).
% 0.42/0.61  thf('62', plain, (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.42/0.61      inference('sat_resolution*', [status(thm)], ['22', '60', '61'])).
% 0.42/0.61  thf('63', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.42/0.61      inference('simpl_trail', [status(thm)], ['20', '62'])).
% 0.42/0.61  thf('64', plain, ((r1_xboole_0 @ sk_B @ sk_B)),
% 0.42/0.61      inference('sup+', [status(thm)], ['14', '63'])).
% 0.42/0.61  thf(t66_xboole_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.42/0.61       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.42/0.61  thf('65', plain,
% 0.42/0.61      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X9 @ X9))),
% 0.42/0.61      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.42/0.61  thf('66', plain, (((sk_B) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['64', '65'])).
% 0.42/0.61  thf('67', plain, (![X21 : $i]: ((k1_subset_1 @ X21) = (k1_xboole_0))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.42/0.61  thf('68', plain,
% 0.42/0.61      ((((sk_B) != (k1_subset_1 @ sk_A)))
% 0.42/0.61         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.42/0.61      inference('split', [status(esa)], ['21'])).
% 0.42/0.61  thf('69', plain,
% 0.42/0.61      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['67', '68'])).
% 0.42/0.61  thf('70', plain, (~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.42/0.61      inference('sat_resolution*', [status(thm)], ['22', '60'])).
% 0.42/0.61  thf('71', plain, (((sk_B) != (k1_xboole_0))),
% 0.42/0.61      inference('simpl_trail', [status(thm)], ['69', '70'])).
% 0.42/0.61  thf('72', plain, ($false),
% 0.42/0.61      inference('simplify_reflect-', [status(thm)], ['66', '71'])).
% 0.42/0.61  
% 0.42/0.61  % SZS output end Refutation
% 0.42/0.61  
% 0.47/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
