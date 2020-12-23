%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0427+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i8zxmhU6NV

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:53 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 112 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :   18
%              Number of atoms          :  610 (1283 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_setfam_1_type,type,(
    k8_setfam_1: $i > $i > $i )).

thf(t59_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ( r1_tarski @ B @ C )
             => ( r1_tarski @ ( k8_setfam_1 @ A @ C ) @ ( k8_setfam_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t59_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k8_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k8_setfam_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_setfam_1])).

thf('4',plain,(
    m1_subset_1 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t58_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( r2_hidden @ B @ A )
       => ( ( r2_hidden @ B @ ( k8_setfam_1 @ A @ C ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
             => ( r2_hidden @ B @ D ) ) ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ( r2_hidden @ X9 @ ( k8_setfam_1 @ X10 @ X11 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X9 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t58_setfam_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_B @ X0 ) @ sk_B )
      | ( r2_hidden @ X0 @ ( k8_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) @ ( k8_setfam_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( sk_C @ X0 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ ( sk_C @ ( k8_setfam_1 @ sk_A @ sk_B ) @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ) @ sk_B )
    | ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ sk_B @ ( sk_C @ ( k8_setfam_1 @ sk_A @ sk_B ) @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ) @ sk_B ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ ( sk_D @ sk_B @ ( sk_C @ ( k8_setfam_1 @ sk_A @ sk_B ) @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ) @ sk_B ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ ( sk_D @ sk_B @ ( sk_C @ ( k8_setfam_1 @ sk_A @ sk_B ) @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ X9 @ X12 )
      | ~ ( r2_hidden @ X9 @ ( k8_setfam_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t58_setfam_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) @ sk_A )
      | ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) @ X1 )
      | ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) @ X1 )
      | ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) @ ( sk_D @ sk_B @ ( sk_C @ ( k8_setfam_1 @ sk_A @ sk_B ) @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ( r2_hidden @ X9 @ ( k8_setfam_1 @ X10 @ X11 ) )
      | ~ ( r2_hidden @ X9 @ ( sk_D @ X11 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t58_setfam_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_D @ sk_B @ X0 ) )
      | ( r2_hidden @ X0 @ ( k8_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_C @ ( k8_setfam_1 @ sk_A @ sk_B ) @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( k8_setfam_1 @ sk_A @ sk_B ) @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r2_hidden @ ( sk_C @ ( k8_setfam_1 @ sk_A @ sk_B ) @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) @ ( k8_setfam_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_C @ ( k8_setfam_1 @ sk_A @ sk_B ) @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_C @ ( k8_setfam_1 @ sk_A @ sk_B ) @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','38'])).

thf('40',plain,(
    ~ ( r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r2_hidden @ ( sk_C @ ( k8_setfam_1 @ sk_A @ sk_B ) @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    r1_tarski @ ( k8_setfam_1 @ sk_A @ sk_C_1 ) @ ( k8_setfam_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).


%------------------------------------------------------------------------------
