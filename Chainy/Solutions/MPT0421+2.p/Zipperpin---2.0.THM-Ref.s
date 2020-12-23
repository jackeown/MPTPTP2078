%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0421+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8ayk33xwvH

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:55 EST 2020

% Result     : Theorem 8.29s
% Output     : Refutation 8.29s
% Verified   : 
% Statistics : Number of formulae       :   20 (  27 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :  121 ( 253 expanded)
%              Number of equality atoms :   13 (  26 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_10_type,type,(
    sk_B_10: $i )).

thf(sk_C_24_type,type,(
    sk_C_24: $i )).

thf(t53_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
         => ( ( ( k7_setfam_1 @ ( A @ B ) )
              = ( k7_setfam_1 @ ( A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
           => ( ( ( k7_setfam_1 @ ( A @ B ) )
                = ( k7_setfam_1 @ ( A @ C ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_setfam_1])).

thf('0',plain,(
    m1_subset_1 @ ( sk_B_10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
     => ( ( k7_setfam_1 @ ( A @ ( k7_setfam_1 @ ( A @ B ) ) ) )
        = B ) ) )).

thf('1',plain,(
    ! [X1894: $i,X1895: $i] :
      ( ( ( k7_setfam_1 @ ( X1895 @ ( k7_setfam_1 @ ( X1895 @ X1894 ) ) ) )
        = X1894 )
      | ~ ( m1_subset_1 @ ( X1894 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1895 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('2',plain,
    ( ( k7_setfam_1 @ ( sk_A_2 @ ( k7_setfam_1 @ ( sk_A_2 @ sk_B_10 ) ) ) )
    = sk_B_10 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ ( sk_C_24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X1894: $i,X1895: $i] :
      ( ( ( k7_setfam_1 @ ( X1895 @ ( k7_setfam_1 @ ( X1895 @ X1894 ) ) ) )
        = X1894 )
      | ~ ( m1_subset_1 @ ( X1894 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1895 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('5',plain,
    ( ( k7_setfam_1 @ ( sk_A_2 @ ( k7_setfam_1 @ ( sk_A_2 @ sk_C_24 ) ) ) )
    = sk_C_24 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k7_setfam_1 @ ( sk_A_2 @ sk_B_10 ) )
    = ( k7_setfam_1 @ ( sk_A_2 @ sk_C_24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k7_setfam_1 @ ( sk_A_2 @ ( k7_setfam_1 @ ( sk_A_2 @ sk_B_10 ) ) ) )
    = sk_C_24 ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    sk_B_10 = sk_C_24 ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    sk_B_10 != sk_C_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

%------------------------------------------------------------------------------
