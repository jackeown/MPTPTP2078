%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KkuQtIMeoA

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:13 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 132 expanded)
%              Number of leaves         :   25 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  643 (1207 expanded)
%              Number of equality atoms :   38 (  74 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k7_setfam_1 @ X14 @ ( k7_setfam_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('2',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('5',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t11_tops_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
          = ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( ( k6_setfam_1 @ X27 @ ( k7_setfam_1 @ X27 @ X26 ) )
        = ( k3_subset_1 @ X27 @ ( k5_setfam_1 @ X27 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[t11_tops_2])).

thf('7',plain,
    ( ( ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
      = ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('9',plain,
    ( ( ( k6_setfam_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('12',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X7 @ ( k3_subset_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('14',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) )
    = ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k3_subset_1 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) )
      = ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k3_subset_1 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D @ X0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t49_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) )
          <=> ( r2_hidden @ C @ B ) ) ) ) )).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r2_hidden @ X18 @ X20 )
      | ( r2_hidden @ ( k3_subset_1 @ X19 @ X18 ) @ ( k7_setfam_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t49_setfam_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ X0 @ X1 ) @ ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k7_setfam_1 @ X14 @ ( k7_setfam_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ X0 @ X1 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['29'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('46',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( m1_subset_1 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','48'])).

thf('50',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['2','17','49'])).

thf('51',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KkuQtIMeoA
% 0.15/0.37  % Computer   : n008.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 09:53:00 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 254 iterations in 0.149s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.62  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.42/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.62  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.42/0.62  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.42/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.62  thf(t12_tops_2, conjecture,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.62       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.42/0.62         ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.42/0.62           ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i,B:$i]:
% 0.42/0.62        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.62          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.42/0.62            ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.42/0.62              ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t12_tops_2])).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(involutiveness_k7_setfam_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.62       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      (![X13 : $i, X14 : $i]:
% 0.42/0.62         (((k7_setfam_1 @ X14 @ (k7_setfam_1 @ X14 @ X13)) = (X13))
% 0.42/0.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.42/0.62      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(dt_k7_setfam_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.62       ( m1_subset_1 @
% 0.42/0.62         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.42/0.62  thf('4', plain,
% 0.42/0.62      (![X11 : $i, X12 : $i]:
% 0.42/0.62         ((m1_subset_1 @ (k7_setfam_1 @ X11 @ X12) @ 
% 0.42/0.62           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11)))
% 0.42/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.42/0.62        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.42/0.62  thf(t11_tops_2, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.62       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.42/0.62         ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.42/0.62           ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ))).
% 0.42/0.62  thf('6', plain,
% 0.42/0.62      (![X26 : $i, X27 : $i]:
% 0.42/0.62         (((X26) = (k1_xboole_0))
% 0.42/0.62          | ((k6_setfam_1 @ X27 @ (k7_setfam_1 @ X27 @ X26))
% 0.42/0.62              = (k3_subset_1 @ X27 @ (k5_setfam_1 @ X27 @ X26)))
% 0.42/0.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X27))))),
% 0.42/0.62      inference('cnf', [status(esa)], [t11_tops_2])).
% 0.42/0.62  thf('7', plain,
% 0.42/0.62      ((((k6_setfam_1 @ sk_A @ 
% 0.42/0.62          (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.42/0.62          = (k3_subset_1 @ sk_A @ 
% 0.42/0.62             (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))
% 0.42/0.62        | ((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.62  thf('8', plain,
% 0.42/0.62      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      ((((k6_setfam_1 @ sk_A @ sk_B)
% 0.42/0.62          = (k3_subset_1 @ sk_A @ 
% 0.42/0.62             (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))
% 0.42/0.62        | ((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['7', '8'])).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.42/0.62        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.42/0.62  thf(dt_k5_setfam_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.62       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      (![X9 : $i, X10 : $i]:
% 0.42/0.62         ((m1_subset_1 @ (k5_setfam_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.42/0.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.42/0.62  thf('12', plain,
% 0.42/0.62      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) @ 
% 0.42/0.62        (k1_zfmisc_1 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.42/0.62  thf(involutiveness_k3_subset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.62       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.42/0.62  thf('13', plain,
% 0.42/0.62      (![X6 : $i, X7 : $i]:
% 0.42/0.62         (((k3_subset_1 @ X7 @ (k3_subset_1 @ X7 @ X6)) = (X6))
% 0.42/0.62          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.42/0.62      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      (((k3_subset_1 @ sk_A @ 
% 0.42/0.62         (k3_subset_1 @ sk_A @ 
% 0.42/0.62          (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))
% 0.42/0.62         = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.42/0.62  thf('15', plain,
% 0.42/0.62      ((((k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B))
% 0.42/0.62          = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.42/0.62        | ((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup+', [status(thm)], ['9', '14'])).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.42/0.62         != (k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('17', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.42/0.62  thf(d5_xboole_0, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.42/0.62       ( ![D:$i]:
% 0.42/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.42/0.62           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.42/0.62  thf('18', plain,
% 0.42/0.62      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.42/0.62         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.42/0.62          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.42/0.62          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.42/0.62      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.42/0.62  thf(t4_subset_1, axiom,
% 0.42/0.62    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.42/0.62  thf('19', plain,
% 0.42/0.62      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.42/0.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.42/0.62  thf(t3_subset, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i]:
% 0.42/0.62         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.62  thf('21', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.42/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.42/0.62  thf('22', plain,
% 0.42/0.62      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.42/0.62         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.42/0.62          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.42/0.62          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.42/0.62      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.42/0.62  thf('23', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.42/0.62          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.42/0.62      inference('eq_fact', [status(thm)], ['22'])).
% 0.42/0.62  thf(t7_ordinal1, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      (![X24 : $i, X25 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 0.42/0.62      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.42/0.62          | ~ (r1_tarski @ X0 @ (sk_D @ X0 @ X1 @ X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['21', '25'])).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X4 @ X3)
% 0.42/0.62          | ~ (r2_hidden @ X4 @ X2)
% 0.42/0.62          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.42/0.62      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X4 @ X2)
% 0.42/0.62          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['27'])).
% 0.42/0.62  thf('29', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['26', '28'])).
% 0.42/0.62  thf('30', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.42/0.62      inference('condensation', [status(thm)], ['29'])).
% 0.42/0.62  thf('31', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.42/0.62          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['18', '30'])).
% 0.42/0.62  thf('32', plain,
% 0.42/0.62      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['21', '25'])).
% 0.42/0.62  thf('33', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.42/0.62          | ((X1) = (k1_xboole_0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['31', '32'])).
% 0.42/0.62  thf('34', plain,
% 0.42/0.62      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.42/0.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.42/0.62  thf('35', plain,
% 0.42/0.62      (![X11 : $i, X12 : $i]:
% 0.42/0.62         ((m1_subset_1 @ (k7_setfam_1 @ X11 @ X12) @ 
% 0.42/0.62           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11)))
% 0.42/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.42/0.62      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.42/0.62  thf('36', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (m1_subset_1 @ (k7_setfam_1 @ X0 @ k1_xboole_0) @ 
% 0.42/0.62          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.42/0.62  thf(t49_setfam_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.62       ( ![C:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.62           ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 0.42/0.62             ( r2_hidden @ C @ B ) ) ) ) ))).
% 0.42/0.62  thf('37', plain,
% 0.42/0.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.42/0.62          | ~ (r2_hidden @ X18 @ X20)
% 0.42/0.62          | (r2_hidden @ (k3_subset_1 @ X19 @ X18) @ (k7_setfam_1 @ X19 @ X20))
% 0.42/0.62          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.42/0.62      inference('cnf', [status(esa)], [t49_setfam_1])).
% 0.42/0.62  thf('38', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((r2_hidden @ (k3_subset_1 @ X0 @ X1) @ 
% 0.42/0.62           (k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ k1_xboole_0)))
% 0.42/0.62          | ~ (r2_hidden @ X1 @ (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.42/0.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.42/0.62  thf('39', plain,
% 0.42/0.62      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.42/0.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.42/0.62  thf('40', plain,
% 0.42/0.62      (![X13 : $i, X14 : $i]:
% 0.42/0.62         (((k7_setfam_1 @ X14 @ (k7_setfam_1 @ X14 @ X13)) = (X13))
% 0.42/0.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.42/0.62      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.42/0.62  thf('41', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.42/0.62  thf('42', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((r2_hidden @ (k3_subset_1 @ X0 @ X1) @ k1_xboole_0)
% 0.42/0.62          | ~ (r2_hidden @ X1 @ (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.42/0.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['38', '41'])).
% 0.42/0.62  thf('43', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.42/0.62      inference('condensation', [status(thm)], ['29'])).
% 0.42/0.62  thf('44', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.42/0.62          | ~ (r2_hidden @ X1 @ (k7_setfam_1 @ X0 @ k1_xboole_0)))),
% 0.42/0.62      inference('clc', [status(thm)], ['42', '43'])).
% 0.42/0.62  thf('45', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (m1_subset_1 @ (k7_setfam_1 @ X0 @ k1_xboole_0) @ 
% 0.42/0.62          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.42/0.62  thf(t4_subset, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.42/0.62       ( m1_subset_1 @ A @ C ) ))).
% 0.42/0.62  thf('46', plain,
% 0.42/0.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X21 @ X22)
% 0.42/0.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.42/0.62          | (m1_subset_1 @ X21 @ X23))),
% 0.42/0.62      inference('cnf', [status(esa)], [t4_subset])).
% 0.42/0.62  thf('47', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.42/0.62          | ~ (r2_hidden @ X1 @ (k7_setfam_1 @ X0 @ k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.42/0.62  thf('48', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ~ (r2_hidden @ X1 @ (k7_setfam_1 @ X0 @ k1_xboole_0))),
% 0.42/0.62      inference('clc', [status(thm)], ['44', '47'])).
% 0.42/0.62  thf('49', plain,
% 0.42/0.62      (![X0 : $i]: ((k7_setfam_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['33', '48'])).
% 0.42/0.62  thf('50', plain, (((k1_xboole_0) = (sk_B))),
% 0.42/0.62      inference('demod', [status(thm)], ['2', '17', '49'])).
% 0.42/0.62  thf('51', plain, (((sk_B) != (k1_xboole_0))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('52', plain, ($false),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.42/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
