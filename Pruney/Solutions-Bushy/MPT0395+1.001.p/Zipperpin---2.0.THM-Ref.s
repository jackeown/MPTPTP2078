%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0395+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WcR8z4OqDb

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  66 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  298 ( 414 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t17_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_setfam_1 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_setfam_1 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t17_setfam_1])).

thf('0',plain,(
    ~ ( r1_setfam_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf(reflexivity_r1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_setfam_1 @ A @ A ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( r1_setfam_1 @ X5 @ X5 ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_setfam_1 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_D @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_setfam_1 @ sk_A @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X5: $i] :
      ( r1_setfam_1 @ X5 @ X5 ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_setfam_1])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_setfam_1 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ ( sk_D @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_setfam_1 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ~ ( r1_setfam_1 @ X0 @ X2 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ ( sk_C @ X1 @ X0 ) @ X0 ) )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_setfam_1 @ X2 @ X3 )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r1_tarski @ ( sk_C @ X3 @ X2 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( sk_C @ X1 @ X0 ) @ X0 ) @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r1_setfam_1 @ sk_A @ sk_B )
    | ( r1_setfam_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,
    ( ( r1_setfam_1 @ sk_A @ sk_B )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ~ ( r1_setfam_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['6','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_setfam_1 @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['1','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['0','31'])).


%------------------------------------------------------------------------------
