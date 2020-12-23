%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MW4tspDTJn

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 115 expanded)
%              Number of leaves         :   30 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  605 ( 844 expanded)
%              Number of equality atoms :   47 (  81 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('1',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t46_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ( ( k7_setfam_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ~ ( ( B != k1_xboole_0 )
            & ( ( k7_setfam_1 @ A @ B )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_setfam_1])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( m1_subset_1 @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    r1_tarski @ ( sk_B @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( sk_B @ sk_B_1 ) @ sk_A )
    = ( sk_B @ sk_B_1 ) ),
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

thf('13',plain,
    ( ( k3_xboole_0 @ sk_A @ ( sk_B @ sk_B_1 ) )
    = ( sk_B @ sk_B_1 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X15 @ X16 )
        = ( k4_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X15 @ X16 )
        = ( k6_subset_1 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( C
              = ( k7_setfam_1 @ A @ B ) )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ C )
                <=> ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) )
      | ( X21
       != ( k7_setfam_1 @ X22 @ X23 ) )
      | ( r2_hidden @ X24 @ X21 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X22 @ X24 ) @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X22 @ X24 ) @ X23 )
      | ( r2_hidden @ X24 @ ( k7_setfam_1 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ ( k6_subset_1 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','37','38','39'])).

thf('41',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('42',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('44',plain,(
    ! [X14: $i] :
      ( r1_xboole_0 @ X14 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('45',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k6_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ X0 ) ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','46'])).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ ( k6_subset_1 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k6_subset_1 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X17: $i,X18: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['47','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','52'])).

thf('54',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','53'])).

thf('55',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','54'])).

thf('56',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MW4tspDTJn
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:19:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.59  % Solved by: fo/fo7.sh
% 0.20/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.59  % done 479 iterations in 0.139s
% 0.20/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.59  % SZS output start Refutation
% 0.20/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.59  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.59  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.59  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.20/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.59  thf(t7_xboole_0, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.59          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.59  thf('0', plain,
% 0.20/0.59      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.20/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.59  thf('1', plain,
% 0.20/0.59      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.20/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.59  thf(t46_setfam_1, conjecture,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.59       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.59            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.59    (~( ![A:$i,B:$i]:
% 0.20/0.59        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.59          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.59               ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.20/0.59    inference('cnf.neg', [status(esa)], [t46_setfam_1])).
% 0.20/0.59  thf('2', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(t4_subset, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.59       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.59  thf('3', plain,
% 0.20/0.59      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X30 @ X31)
% 0.20/0.59          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.20/0.59          | (m1_subset_1 @ X30 @ X32))),
% 0.20/0.59      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.59  thf('4', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.59          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.59  thf('5', plain,
% 0.20/0.59      ((((sk_B_1) = (k1_xboole_0))
% 0.20/0.59        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.59  thf('6', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('7', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.59      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.20/0.59  thf(t3_subset, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.59  thf('8', plain,
% 0.20/0.59      (![X27 : $i, X28 : $i]:
% 0.20/0.59         ((r1_tarski @ X27 @ X28) | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.59  thf('9', plain, ((r1_tarski @ (sk_B @ sk_B_1) @ sk_A)),
% 0.20/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.59  thf(t28_xboole_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.59  thf('10', plain,
% 0.20/0.59      (![X9 : $i, X10 : $i]:
% 0.20/0.59         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.20/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.59  thf('11', plain,
% 0.20/0.59      (((k3_xboole_0 @ (sk_B @ sk_B_1) @ sk_A) = (sk_B @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.59  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.59  thf('12', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.59  thf('13', plain,
% 0.20/0.59      (((k3_xboole_0 @ sk_A @ (sk_B @ sk_B_1)) = (sk_B @ sk_B_1))),
% 0.20/0.59      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.59  thf('14', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.59  thf(dt_k6_subset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.59  thf('15', plain,
% 0.20/0.59      (![X17 : $i, X18 : $i]:
% 0.20/0.59         (m1_subset_1 @ (k6_subset_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))),
% 0.20/0.59      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.20/0.59  thf(d5_subset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.59       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.59  thf('16', plain,
% 0.20/0.59      (![X15 : $i, X16 : $i]:
% 0.20/0.59         (((k3_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))
% 0.20/0.59          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.20/0.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.59  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.59  thf('17', plain,
% 0.20/0.59      (![X19 : $i, X20 : $i]:
% 0.20/0.59         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.59  thf('18', plain,
% 0.20/0.59      (![X15 : $i, X16 : $i]:
% 0.20/0.59         (((k3_subset_1 @ X15 @ X16) = (k6_subset_1 @ X15 @ X16))
% 0.20/0.59          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.20/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.59  thf('19', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.20/0.59           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['15', '18'])).
% 0.20/0.59  thf('20', plain, (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(d8_setfam_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.59       ( ![C:$i]:
% 0.20/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.59           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.20/0.59             ( ![D:$i]:
% 0.20/0.59               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.59                 ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.59                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.20/0.59  thf('21', plain,
% 0.20/0.59      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22)))
% 0.20/0.59          | ((X21) != (k7_setfam_1 @ X22 @ X23))
% 0.20/0.59          | (r2_hidden @ X24 @ X21)
% 0.20/0.59          | ~ (r2_hidden @ (k3_subset_1 @ X22 @ X24) @ X23)
% 0.20/0.59          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X22))
% 0.20/0.59          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.20/0.59      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.20/0.59  thf('22', plain,
% 0.20/0.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22)))
% 0.20/0.59          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X22))
% 0.20/0.59          | ~ (r2_hidden @ (k3_subset_1 @ X22 @ X24) @ X23)
% 0.20/0.59          | (r2_hidden @ X24 @ (k7_setfam_1 @ X22 @ X23))
% 0.20/0.59          | ~ (m1_subset_1 @ (k7_setfam_1 @ X22 @ X23) @ 
% 0.20/0.59               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.20/0.59      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.59  thf('23', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.59          | (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B_1))
% 0.20/0.59          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B_1)
% 0.20/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.59          | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['20', '22'])).
% 0.20/0.59  thf(t2_boole, axiom,
% 0.20/0.59    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.59  thf('24', plain,
% 0.20/0.59      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.59      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.59  thf(t100_xboole_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.59  thf('25', plain,
% 0.20/0.59      (![X7 : $i, X8 : $i]:
% 0.20/0.59         ((k4_xboole_0 @ X7 @ X8)
% 0.20/0.59           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.59  thf('26', plain,
% 0.20/0.59      (![X19 : $i, X20 : $i]:
% 0.20/0.59         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.59  thf('27', plain,
% 0.20/0.59      (![X7 : $i, X8 : $i]:
% 0.20/0.59         ((k6_subset_1 @ X7 @ X8)
% 0.20/0.59           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.20/0.59      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.59  thf('28', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((k6_subset_1 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.59      inference('sup+', [status(thm)], ['24', '27'])).
% 0.20/0.59  thf(t48_xboole_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.59  thf('29', plain,
% 0.20/0.59      (![X12 : $i, X13 : $i]:
% 0.20/0.59         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.20/0.59           = (k3_xboole_0 @ X12 @ X13))),
% 0.20/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.59  thf('30', plain,
% 0.20/0.59      (![X19 : $i, X20 : $i]:
% 0.20/0.59         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.59  thf('31', plain,
% 0.20/0.59      (![X19 : $i, X20 : $i]:
% 0.20/0.59         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.59  thf('32', plain,
% 0.20/0.59      (![X12 : $i, X13 : $i]:
% 0.20/0.59         ((k6_subset_1 @ X12 @ (k6_subset_1 @ X12 @ X13))
% 0.20/0.59           = (k3_xboole_0 @ X12 @ X13))),
% 0.20/0.59      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.59  thf('33', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((k6_subset_1 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.20/0.59           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.59      inference('sup+', [status(thm)], ['28', '32'])).
% 0.20/0.59  thf('34', plain,
% 0.20/0.59      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.59      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.59  thf('35', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((k6_subset_1 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.59      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.59  thf('36', plain,
% 0.20/0.59      (![X17 : $i, X18 : $i]:
% 0.20/0.59         (m1_subset_1 @ (k6_subset_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))),
% 0.20/0.59      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.20/0.59  thf('37', plain,
% 0.20/0.59      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.59      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.59  thf('38', plain, (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('39', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('40', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.20/0.59          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B_1)
% 0.20/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['23', '37', '38', '39'])).
% 0.20/0.59  thf('41', plain,
% 0.20/0.59      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.59      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.59  thf(t4_xboole_0, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.59            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.59  thf('42', plain,
% 0.20/0.59      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.20/0.59          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.20/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.59  thf('43', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.59  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.59  thf('44', plain, (![X14 : $i]: (r1_xboole_0 @ X14 @ k1_xboole_0)),
% 0.20/0.59      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.59  thf('45', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.59      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.59  thf('46', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.59          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B_1))),
% 0.20/0.59      inference('clc', [status(thm)], ['40', '45'])).
% 0.20/0.59  thf('47', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (r2_hidden @ (k6_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ X0)) @ 
% 0.20/0.59             sk_B_1)
% 0.20/0.59          | ~ (m1_subset_1 @ (k6_subset_1 @ sk_A @ X0) @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['19', '46'])).
% 0.20/0.59  thf('48', plain,
% 0.20/0.59      (![X12 : $i, X13 : $i]:
% 0.20/0.59         ((k6_subset_1 @ X12 @ (k6_subset_1 @ X12 @ X13))
% 0.20/0.59           = (k3_xboole_0 @ X12 @ X13))),
% 0.20/0.59      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.59  thf('49', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.59  thf('50', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((k3_xboole_0 @ X0 @ X1)
% 0.20/0.59           = (k6_subset_1 @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 0.20/0.59      inference('sup+', [status(thm)], ['48', '49'])).
% 0.20/0.59  thf('51', plain,
% 0.20/0.59      (![X17 : $i, X18 : $i]:
% 0.20/0.59         (m1_subset_1 @ (k6_subset_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))),
% 0.20/0.59      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.20/0.59  thf('52', plain,
% 0.20/0.59      (![X0 : $i]: ~ (r2_hidden @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B_1)),
% 0.20/0.59      inference('demod', [status(thm)], ['47', '50', '51'])).
% 0.20/0.59  thf('53', plain,
% 0.20/0.59      (![X0 : $i]: ~ (r2_hidden @ (k3_xboole_0 @ sk_A @ X0) @ sk_B_1)),
% 0.20/0.59      inference('sup-', [status(thm)], ['14', '52'])).
% 0.20/0.59  thf('54', plain, (~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.20/0.59      inference('sup-', [status(thm)], ['13', '53'])).
% 0.20/0.59  thf('55', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['0', '54'])).
% 0.20/0.59  thf('56', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('57', plain, ($false),
% 0.20/0.59      inference('simplify_reflect-', [status(thm)], ['55', '56'])).
% 0.20/0.59  
% 0.20/0.59  % SZS output end Refutation
% 0.20/0.59  
% 0.20/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
