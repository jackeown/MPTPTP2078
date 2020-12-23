%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0813+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wpeoY1APP8

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:01 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   34 (  45 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  186 ( 329 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(sk_D_76_type,type,(
    sk_D_76: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_91_type,type,(
    sk_C_91: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_57_type,type,(
    sk_B_57: $i )).

thf(t4_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ ( D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( B @ C ) ) ) ) )
     => ( ( r1_tarski @ ( A @ D ) )
       => ( m1_subset_1 @ ( A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ ( D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( B @ C ) ) ) ) )
       => ( ( r1_tarski @ ( A @ D ) )
         => ( m1_subset_1 @ ( A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( sk_A_14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_C_91 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ ( sk_D_76 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_C_91 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( A @ ( k1_zfmisc_1 @ B ) ) )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('2',plain,(
    ! [X1964: $i,X1965: $i] :
      ( ( r1_tarski @ ( X1964 @ X1965 ) )
      | ~ ( m1_subset_1 @ ( X1964 @ ( k1_zfmisc_1 @ X1965 ) ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ ( sk_D_76 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_C_91 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ ( A @ B ) )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( A != B ) ) ) )).

thf('4',plain,(
    ! [X40: $i,X42: $i] :
      ( ( r2_xboole_0 @ ( X40 @ X42 ) )
      | ( X40 = X42 )
      | ~ ( r1_tarski @ ( X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('5',plain,
    ( ( sk_D_76
      = ( k2_zfmisc_1 @ ( sk_B_57 @ sk_C_91 ) ) )
    | ( r2_xboole_0 @ ( sk_D_76 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_C_91 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( sk_A_14 @ sk_D_76 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l58_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r2_xboole_0 @ ( B @ C ) ) )
     => ( r2_xboole_0 @ ( A @ C ) ) ) )).

thf('7',plain,(
    ! [X94: $i,X95: $i,X96: $i] :
      ( ~ ( r1_tarski @ ( X94 @ X95 ) )
      | ~ ( r2_xboole_0 @ ( X95 @ X96 ) )
      | ( r2_xboole_0 @ ( X94 @ X96 ) ) ) ),
    inference(cnf,[status(esa)],[l58_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_xboole_0 @ ( sk_A_14 @ X0 ) )
      | ~ ( r2_xboole_0 @ ( sk_D_76 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_D_76
      = ( k2_zfmisc_1 @ ( sk_B_57 @ sk_C_91 ) ) )
    | ( r2_xboole_0 @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_C_91 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ ( X40 @ X41 ) )
      | ~ ( r2_xboole_0 @ ( X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('11',plain,
    ( ( sk_D_76
      = ( k2_zfmisc_1 @ ( sk_B_57 @ sk_C_91 ) ) )
    | ( r1_tarski @ ( sk_A_14 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_C_91 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1964: $i,X1966: $i] :
      ( ( m1_subset_1 @ ( X1964 @ ( k1_zfmisc_1 @ X1966 ) ) )
      | ~ ( r1_tarski @ ( X1964 @ X1966 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,
    ( ( sk_D_76
      = ( k2_zfmisc_1 @ ( sk_B_57 @ sk_C_91 ) ) )
    | ( m1_subset_1 @ ( sk_A_14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_C_91 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( m1_subset_1 @ ( sk_A_14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_C_91 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( sk_D_76
    = ( k2_zfmisc_1 @ ( sk_B_57 @ sk_C_91 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( sk_A_14 @ sk_D_76 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X1964: $i,X1966: $i] :
      ( ( m1_subset_1 @ ( X1964 @ ( k1_zfmisc_1 @ X1966 ) ) )
      | ~ ( r1_tarski @ ( X1964 @ X1966 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    m1_subset_1 @ ( sk_A_14 @ ( k1_zfmisc_1 @ sk_D_76 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15','18'])).

%------------------------------------------------------------------------------
