%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PPorDD85zt

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 961 expanded)
%              Number of leaves         :   19 ( 283 expanded)
%              Depth                    :   29
%              Number of atoms          : 1913 (18208 expanded)
%              Number of equality atoms :    5 ( 282 expanded)
%              Maximal formula depth    :   18 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t54_relset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
         => ( ! [D: $i] :
                ( ( r2_hidden @ D @ A )
               => ( ( k11_relat_1 @ B @ D )
                  = ( k11_relat_1 @ C @ D ) ) )
           => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
           => ( ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( ( k11_relat_1 @ B @ D )
                    = ( k11_relat_1 @ C @ D ) ) )
             => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t54_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ! [D: $i] :
          ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( r2_relset_1 @ A @ B @ C @ D )
          <=> ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ! [F: $i] :
                    ( ( m1_subset_1 @ F @ B )
                   => ( ( r2_hidden @ ( k4_tarski @ E @ F ) @ C )
                    <=> ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X14 @ X17 @ X16 @ X15 ) @ ( sk_F @ X14 @ X17 @ X16 @ X15 ) ) @ X17 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X14 @ X17 @ X16 @ X15 ) @ ( sk_F @ X14 @ X17 @ X16 @ X15 ) ) @ X14 )
      | ( r2_relset_1 @ X15 @ X16 @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ X0 @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ X0 @ sk_A @ sk_A ) ) @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ X0 @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ X0 @ sk_A @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_C )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( r2_relset_1 @ X15 @ X16 @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X18 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X18 ) @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X18 ) @ X17 )
      | ~ ( m1_subset_1 @ X19 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_relset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ sk_B )
      | ~ ( m1_subset_1 @ X2 @ sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X14 @ X17 @ X16 @ X15 ) @ ( sk_F @ X14 @ X17 @ X16 @ X15 ) ) @ X17 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X14 @ X17 @ X16 @ X15 ) @ ( sk_F @ X14 @ X17 @ X16 @ X15 ) ) @ X14 )
      | ( r2_relset_1 @ X15 @ X16 @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_relset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ X0 @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ X0 @ sk_A @ sk_A ) ) @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ X0 @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ X0 @ sk_A @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_B )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X8 ) @ X9 )
      | ( r2_hidden @ X8 @ ( k11_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('18',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('28',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) )
    | ( r2_hidden @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k11_relat_1 @ X9 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('30',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ sk_A )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('32',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ sk_A )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_hidden @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ sk_A )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('38',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ sk_A )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X20: $i] :
      ( ( ( k11_relat_1 @ sk_B @ X20 )
        = ( k11_relat_1 @ sk_C @ X20 ) )
      | ~ ( r2_hidden @ X20 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) )
      = ( k11_relat_1 @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('42',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X8 ) @ X9 )
      | ( r2_hidden @ X8 @ ( k11_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('43',plain,
    ( ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,
    ( ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) )
      = ( k11_relat_1 @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('51',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k11_relat_1 @ X9 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ X0 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_C )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_C )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ X14 @ X17 @ X16 @ X15 ) @ ( sk_F @ X14 @ X17 @ X16 @ X15 ) ) @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ X14 @ X17 @ X16 @ X15 ) @ ( sk_F @ X14 @ X17 @ X16 @ X15 ) ) @ X14 )
      | ( r2_relset_1 @ X15 @ X16 @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_relset_1])).

thf('58',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_B )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('64',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k11_relat_1 @ X9 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('65',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('67',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ),
    inference(clc,[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','68'])).

thf('70',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ sk_A )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( m1_subset_1 @ ( sk_E @ X14 @ X17 @ X16 @ X15 ) @ X15 )
      | ( r2_relset_1 @ X15 @ X16 @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_relset_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_C @ X0 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ sk_A )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( m1_subset_1 @ ( sk_F @ X14 @ X17 @ X16 @ X15 ) @ X16 )
      | ( r2_relset_1 @ X15 @ X16 @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_relset_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_C )
      | ( m1_subset_1 @ ( sk_F @ sk_C @ X0 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( m1_subset_1 @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) @ sk_A )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['70','77','84'])).

thf('86',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_B ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ X14 @ X17 @ X16 @ X15 ) @ ( sk_F @ X14 @ X17 @ X16 @ X15 ) ) @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ X14 @ X17 @ X16 @ X15 ) @ ( sk_F @ X14 @ X17 @ X16 @ X15 ) ) @ X14 )
      | ( r2_relset_1 @ X15 @ X16 @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_relset_1])).

thf('88',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_C ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_B ),
    inference(simplify,[status(thm)],['85'])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( r2_relset_1 @ X15 @ X16 @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X18 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X18 ) @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X18 ) @ X14 )
      | ~ ( m1_subset_1 @ X19 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_relset_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ),
    inference(clc,[status(thm)],['62','67'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ sk_A )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['94','101'])).

thf('103',plain,(
    m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['75','76'])).

thf('104',plain,(
    m1_subset_1 @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['82','83'])).

thf('105',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_C ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['93','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PPorDD85zt
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 91 iterations in 0.072s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.56  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.20/0.56  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.56  thf(t54_relset_1, conjecture,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.56       ( ![C:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.56           ( ( ![D:$i]:
% 0.20/0.56               ( ( r2_hidden @ D @ A ) =>
% 0.20/0.56                 ( ( k11_relat_1 @ B @ D ) = ( k11_relat_1 @ C @ D ) ) ) ) =>
% 0.20/0.56             ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i]:
% 0.20/0.56        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.56          ( ![C:$i]:
% 0.20/0.56            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.56              ( ( ![D:$i]:
% 0.20/0.56                  ( ( r2_hidden @ D @ A ) =>
% 0.20/0.56                    ( ( k11_relat_1 @ B @ D ) = ( k11_relat_1 @ C @ D ) ) ) ) =>
% 0.20/0.56                ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t54_relset_1])).
% 0.20/0.56  thf('0', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(d3_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ![D:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56           ( ( r2_relset_1 @ A @ B @ C @ D ) <=>
% 0.20/0.56             ( ![E:$i]:
% 0.20/0.56               ( ( m1_subset_1 @ E @ A ) =>
% 0.20/0.56                 ( ![F:$i]:
% 0.20/0.56                   ( ( m1_subset_1 @ F @ B ) =>
% 0.20/0.56                     ( ( r2_hidden @ ( k4_tarski @ E @ F ) @ C ) <=>
% 0.20/0.56                       ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.20/0.56          | (r2_hidden @ 
% 0.20/0.56             (k4_tarski @ (sk_E @ X14 @ X17 @ X16 @ X15) @ 
% 0.20/0.56              (sk_F @ X14 @ X17 @ X16 @ X15)) @ 
% 0.20/0.56             X17)
% 0.20/0.56          | (r2_hidden @ 
% 0.20/0.56             (k4_tarski @ (sk_E @ X14 @ X17 @ X16 @ X15) @ 
% 0.20/0.56              (sk_F @ X14 @ X17 @ X16 @ X15)) @ 
% 0.20/0.56             X14)
% 0.20/0.56          | (r2_relset_1 @ X15 @ X16 @ X17 @ X14)
% 0.20/0.56          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_relset_1])).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.56          | (r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_C)
% 0.20/0.56          | (r2_hidden @ 
% 0.20/0.56             (k4_tarski @ (sk_E @ sk_C @ X0 @ sk_A @ sk_A) @ 
% 0.20/0.56              (sk_F @ sk_C @ X0 @ sk_A @ sk_A)) @ 
% 0.20/0.56             sk_C)
% 0.20/0.56          | (r2_hidden @ 
% 0.20/0.56             (k4_tarski @ (sk_E @ sk_C @ X0 @ sk_A @ sk_A) @ 
% 0.20/0.56              (sk_F @ sk_C @ X0 @ sk_A @ sk_A)) @ 
% 0.20/0.56             X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (((r2_hidden @ 
% 0.20/0.56         (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.56          (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.56         sk_B)
% 0.20/0.56        | (r2_hidden @ 
% 0.20/0.56           (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.56            (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.56           sk_C)
% 0.20/0.56        | (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C))),
% 0.20/0.56      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.56  thf('5', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (((r2_hidden @ 
% 0.20/0.56         (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.56          (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.56         sk_C)
% 0.20/0.56        | (r2_hidden @ 
% 0.20/0.56           (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.56            (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.56           sk_B))),
% 0.20/0.56      inference('clc', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.20/0.56          | ~ (r2_relset_1 @ X15 @ X16 @ X17 @ X14)
% 0.20/0.56          | ~ (m1_subset_1 @ X18 @ X16)
% 0.20/0.56          | (r2_hidden @ (k4_tarski @ X19 @ X18) @ X14)
% 0.20/0.56          | ~ (r2_hidden @ (k4_tarski @ X19 @ X18) @ X17)
% 0.20/0.56          | ~ (m1_subset_1 @ X19 @ X15)
% 0.20/0.56          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_relset_1])).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.56          | ~ (m1_subset_1 @ X1 @ sk_A)
% 0.20/0.56          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.20/0.56          | (r2_hidden @ (k4_tarski @ X1 @ X2) @ sk_B)
% 0.20/0.56          | ~ (m1_subset_1 @ X2 @ sk_A)
% 0.20/0.56          | ~ (r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.56          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_B)
% 0.20/0.56          | ~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C)
% 0.20/0.56          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.20/0.56          | (r2_hidden @ 
% 0.20/0.56             (k4_tarski @ (sk_E @ X14 @ X17 @ X16 @ X15) @ 
% 0.20/0.56              (sk_F @ X14 @ X17 @ X16 @ X15)) @ 
% 0.20/0.56             X17)
% 0.20/0.56          | (r2_hidden @ 
% 0.20/0.56             (k4_tarski @ (sk_E @ X14 @ X17 @ X16 @ X15) @ 
% 0.20/0.56              (sk_F @ X14 @ X17 @ X16 @ X15)) @ 
% 0.20/0.56             X14)
% 0.20/0.56          | (r2_relset_1 @ X15 @ X16 @ X17 @ X14)
% 0.20/0.56          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_relset_1])).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.56          | (r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_B)
% 0.20/0.56          | (r2_hidden @ 
% 0.20/0.56             (k4_tarski @ (sk_E @ sk_B @ X0 @ sk_A @ sk_A) @ 
% 0.20/0.56              (sk_F @ sk_B @ X0 @ sk_A @ sk_A)) @ 
% 0.20/0.56             sk_B)
% 0.20/0.56          | (r2_hidden @ 
% 0.20/0.56             (k4_tarski @ (sk_E @ sk_B @ X0 @ sk_A @ sk_A) @ 
% 0.20/0.56              (sk_F @ sk_B @ X0 @ sk_A @ sk_A)) @ 
% 0.20/0.56             X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (((r2_hidden @ 
% 0.20/0.56         (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56          (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.56         sk_C)
% 0.20/0.56        | (r2_hidden @ 
% 0.20/0.56           (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56            (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.56           sk_B)
% 0.20/0.56        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['12', '15'])).
% 0.20/0.56  thf(t204_relat_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ C ) =>
% 0.20/0.56       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.56         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.56         (~ (r2_hidden @ (k4_tarski @ X10 @ X8) @ X9)
% 0.20/0.56          | (r2_hidden @ X8 @ (k11_relat_1 @ X9 @ X10))
% 0.20/0.56          | ~ (v1_relat_1 @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | (r2_hidden @ 
% 0.20/0.56           (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56            (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.56           sk_B)
% 0.20/0.56        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.56        | (r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56           (k11_relat_1 @ sk_C @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(cc1_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( v1_relat_1 @ C ) ))).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.56         ((v1_relat_1 @ X11)
% 0.20/0.56          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.20/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.56  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | (r2_hidden @ 
% 0.20/0.56           (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56            (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.56           sk_B)
% 0.20/0.56        | (r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56           (k11_relat_1 @ sk_C @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))))),
% 0.20/0.56      inference('demod', [status(thm)], ['18', '21'])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(l3_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X5 @ X6)
% 0.20/0.56          | (r2_hidden @ X5 @ X7)
% 0.20/0.56          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.56      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.20/0.56          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (((r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56         (k11_relat_1 @ sk_C @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A)))
% 0.20/0.56        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | (r2_hidden @ 
% 0.20/0.56           (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56            (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.56           (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['22', '25'])).
% 0.20/0.56  thf(l54_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.56     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.20/0.56       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.56         ((r2_hidden @ X0 @ X1)
% 0.20/0.56          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.20/0.56      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | (r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56           (k11_relat_1 @ sk_C @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A)))
% 0.20/0.56        | (r2_hidden @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X8 @ (k11_relat_1 @ X9 @ X10))
% 0.20/0.56          | (r2_hidden @ (k4_tarski @ X10 @ X8) @ X9)
% 0.20/0.56          | ~ (v1_relat_1 @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      (((r2_hidden @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ sk_A)
% 0.20/0.56        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.56        | (r2_hidden @ 
% 0.20/0.56           (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56            (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.56           sk_C))),
% 0.20/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.56  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      (((r2_hidden @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ sk_A)
% 0.20/0.56        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | (r2_hidden @ 
% 0.20/0.56           (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56            (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.56           sk_C))),
% 0.20/0.56      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X5 @ X6)
% 0.20/0.56          | (r2_hidden @ X5 @ X7)
% 0.20/0.56          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.56      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.20/0.56          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.20/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | (r2_hidden @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ sk_A)
% 0.20/0.56        | (r2_hidden @ 
% 0.20/0.56           (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56            (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.56           (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['32', '35'])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.56         ((r2_hidden @ X0 @ X1)
% 0.20/0.56          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.20/0.56      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      (((r2_hidden @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ sk_A)
% 0.20/0.56        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B))),
% 0.20/0.56      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      (![X20 : $i]:
% 0.20/0.56         (((k11_relat_1 @ sk_B @ X20) = (k11_relat_1 @ sk_C @ X20))
% 0.20/0.56          | ~ (r2_hidden @ X20 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | ((k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))
% 0.20/0.56            = (k11_relat_1 @ sk_C @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.56  thf('41', plain,
% 0.20/0.56      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | (r2_hidden @ 
% 0.20/0.56           (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56            (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.56           sk_B)
% 0.20/0.56        | (r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56           (k11_relat_1 @ sk_C @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))))),
% 0.20/0.56      inference('demod', [status(thm)], ['18', '21'])).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.56         (~ (r2_hidden @ (k4_tarski @ X10 @ X8) @ X9)
% 0.20/0.56          | (r2_hidden @ X8 @ (k11_relat_1 @ X9 @ X10))
% 0.20/0.56          | ~ (v1_relat_1 @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      (((r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56         (k11_relat_1 @ sk_C @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A)))
% 0.20/0.56        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.56        | (r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56           (k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.56         ((v1_relat_1 @ X11)
% 0.20/0.56          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.20/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.56  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.56      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (((r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56         (k11_relat_1 @ sk_C @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A)))
% 0.20/0.56        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | (r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56           (k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))))),
% 0.20/0.56      inference('demod', [status(thm)], ['43', '46'])).
% 0.20/0.56  thf('48', plain,
% 0.20/0.56      (((r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56         (k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A)))
% 0.20/0.56        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | (r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56           (k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A)))
% 0.20/0.56        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B))),
% 0.20/0.56      inference('sup+', [status(thm)], ['40', '47'])).
% 0.20/0.56  thf('49', plain,
% 0.20/0.56      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | (r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56           (k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))))),
% 0.20/0.56      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.56  thf('50', plain,
% 0.20/0.56      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | ((k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))
% 0.20/0.56            = (k11_relat_1 @ sk_C @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X8 @ (k11_relat_1 @ X9 @ X10))
% 0.20/0.56          | (r2_hidden @ (k4_tarski @ X10 @ X8) @ X9)
% 0.20/0.56          | ~ (v1_relat_1 @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.56  thf('52', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X0 @ 
% 0.20/0.56             (k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A)))
% 0.20/0.56          | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56          | ~ (v1_relat_1 @ sk_C)
% 0.20/0.56          | (r2_hidden @ 
% 0.20/0.56             (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ X0) @ sk_C))),
% 0.20/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.56  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.56  thf('54', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X0 @ 
% 0.20/0.56             (k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A)))
% 0.20/0.56          | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56          | (r2_hidden @ 
% 0.20/0.56             (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ X0) @ sk_C))),
% 0.20/0.56      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.56  thf('55', plain,
% 0.20/0.56      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | (r2_hidden @ 
% 0.20/0.56           (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56            (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.56           sk_C)
% 0.20/0.56        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['49', '54'])).
% 0.20/0.56  thf('56', plain,
% 0.20/0.56      (((r2_hidden @ 
% 0.20/0.56         (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56          (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.56         sk_C)
% 0.20/0.56        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B))),
% 0.20/0.56      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.56  thf('57', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.20/0.56          | ~ (r2_hidden @ 
% 0.20/0.56               (k4_tarski @ (sk_E @ X14 @ X17 @ X16 @ X15) @ 
% 0.20/0.56                (sk_F @ X14 @ X17 @ X16 @ X15)) @ 
% 0.20/0.56               X17)
% 0.20/0.56          | ~ (r2_hidden @ 
% 0.20/0.56               (k4_tarski @ (sk_E @ X14 @ X17 @ X16 @ X15) @ 
% 0.20/0.56                (sk_F @ X14 @ X17 @ X16 @ X15)) @ 
% 0.20/0.56               X14)
% 0.20/0.56          | (r2_relset_1 @ X15 @ X16 @ X17 @ X14)
% 0.20/0.56          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_relset_1])).
% 0.20/0.56  thf('58', plain,
% 0.20/0.56      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.56        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | ~ (r2_hidden @ 
% 0.20/0.56             (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56              (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.56             sk_B)
% 0.20/0.56        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.56  thf('59', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('60', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('61', plain,
% 0.20/0.56      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | ~ (r2_hidden @ 
% 0.20/0.56             (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56              (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.56             sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.20/0.56  thf('62', plain,
% 0.20/0.56      ((~ (r2_hidden @ 
% 0.20/0.56           (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56            (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.56           sk_B)
% 0.20/0.56        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B))),
% 0.20/0.56      inference('simplify', [status(thm)], ['61'])).
% 0.20/0.56  thf('63', plain,
% 0.20/0.56      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | (r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.56           (k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))))),
% 0.20/0.56      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.56  thf('64', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X8 @ (k11_relat_1 @ X9 @ X10))
% 0.20/0.56          | (r2_hidden @ (k4_tarski @ X10 @ X8) @ X9)
% 0.20/0.56          | ~ (v1_relat_1 @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.56  thf('65', plain,
% 0.20/0.56      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.56        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.56        | (r2_hidden @ 
% 0.20/0.57           (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.57            (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.57           sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.57  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.57      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.57  thf('67', plain,
% 0.20/0.57      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.57        | (r2_hidden @ 
% 0.20/0.57           (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.57            (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.57           sk_B))),
% 0.20/0.57      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.57  thf('68', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)),
% 0.20/0.57      inference('clc', [status(thm)], ['62', '67'])).
% 0.20/0.57  thf('69', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.57          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_B)
% 0.20/0.57          | ~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C)
% 0.20/0.57          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.20/0.57      inference('demod', [status(thm)], ['11', '68'])).
% 0.20/0.57  thf('70', plain,
% 0.20/0.57      (((r2_hidden @ 
% 0.20/0.57         (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.57          (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.57         sk_B)
% 0.20/0.57        | ~ (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ sk_A)
% 0.20/0.57        | (r2_hidden @ 
% 0.20/0.57           (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.57            (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.57           sk_B)
% 0.20/0.57        | ~ (m1_subset_1 @ (sk_F @ sk_C @ sk_B @ sk_A @ sk_A) @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['6', '69'])).
% 0.20/0.57  thf('71', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('72', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('73', plain,
% 0.20/0.57      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.20/0.57          | (m1_subset_1 @ (sk_E @ X14 @ X17 @ X16 @ X15) @ X15)
% 0.20/0.57          | (r2_relset_1 @ X15 @ X16 @ X17 @ X14)
% 0.20/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_relset_1])).
% 0.20/0.57  thf('74', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.57          | (r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_C)
% 0.20/0.57          | (m1_subset_1 @ (sk_E @ sk_C @ X0 @ sk_A @ sk_A) @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.57  thf('75', plain,
% 0.20/0.57      (((m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ sk_A)
% 0.20/0.57        | (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C))),
% 0.20/0.57      inference('sup-', [status(thm)], ['71', '74'])).
% 0.20/0.57  thf('76', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('77', plain, ((m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ sk_A)),
% 0.20/0.57      inference('clc', [status(thm)], ['75', '76'])).
% 0.20/0.57  thf('78', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('79', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('80', plain,
% 0.20/0.57      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.20/0.57          | (m1_subset_1 @ (sk_F @ X14 @ X17 @ X16 @ X15) @ X16)
% 0.20/0.57          | (r2_relset_1 @ X15 @ X16 @ X17 @ X14)
% 0.20/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_relset_1])).
% 0.20/0.57  thf('81', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.57          | (r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_C)
% 0.20/0.57          | (m1_subset_1 @ (sk_F @ sk_C @ X0 @ sk_A @ sk_A) @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.57  thf('82', plain,
% 0.20/0.57      (((m1_subset_1 @ (sk_F @ sk_C @ sk_B @ sk_A @ sk_A) @ sk_A)
% 0.20/0.57        | (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C))),
% 0.20/0.57      inference('sup-', [status(thm)], ['78', '81'])).
% 0.20/0.57  thf('83', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('84', plain, ((m1_subset_1 @ (sk_F @ sk_C @ sk_B @ sk_A @ sk_A) @ sk_A)),
% 0.20/0.57      inference('clc', [status(thm)], ['82', '83'])).
% 0.20/0.57  thf('85', plain,
% 0.20/0.57      (((r2_hidden @ 
% 0.20/0.57         (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.57          (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.57         sk_B)
% 0.20/0.57        | (r2_hidden @ 
% 0.20/0.57           (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.57            (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.57           sk_B))),
% 0.20/0.57      inference('demod', [status(thm)], ['70', '77', '84'])).
% 0.20/0.57  thf('86', plain,
% 0.20/0.57      ((r2_hidden @ 
% 0.20/0.57        (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.57         (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.57        sk_B)),
% 0.20/0.57      inference('simplify', [status(thm)], ['85'])).
% 0.20/0.57  thf('87', plain,
% 0.20/0.57      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.20/0.57          | ~ (r2_hidden @ 
% 0.20/0.57               (k4_tarski @ (sk_E @ X14 @ X17 @ X16 @ X15) @ 
% 0.20/0.57                (sk_F @ X14 @ X17 @ X16 @ X15)) @ 
% 0.20/0.57               X17)
% 0.20/0.57          | ~ (r2_hidden @ 
% 0.20/0.57               (k4_tarski @ (sk_E @ X14 @ X17 @ X16 @ X15) @ 
% 0.20/0.57                (sk_F @ X14 @ X17 @ X16 @ X15)) @ 
% 0.20/0.57               X14)
% 0.20/0.57          | (r2_relset_1 @ X15 @ X16 @ X17 @ X14)
% 0.20/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_relset_1])).
% 0.20/0.57  thf('88', plain,
% 0.20/0.57      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.57        | (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.20/0.57        | ~ (r2_hidden @ 
% 0.20/0.57             (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.57              (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.57             sk_C)
% 0.20/0.57        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['86', '87'])).
% 0.20/0.57  thf('89', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('90', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('91', plain,
% 0.20/0.57      (((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.20/0.57        | ~ (r2_hidden @ 
% 0.20/0.57             (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.57              (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.57             sk_C))),
% 0.20/0.57      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.20/0.57  thf('92', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('93', plain,
% 0.20/0.57      (~ (r2_hidden @ 
% 0.20/0.57          (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.57           (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.57          sk_C)),
% 0.20/0.57      inference('clc', [status(thm)], ['91', '92'])).
% 0.20/0.57  thf('94', plain,
% 0.20/0.57      ((r2_hidden @ 
% 0.20/0.57        (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.57         (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.57        sk_B)),
% 0.20/0.57      inference('simplify', [status(thm)], ['85'])).
% 0.20/0.57  thf('95', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('96', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('97', plain,
% 0.20/0.57      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.20/0.57          | ~ (r2_relset_1 @ X15 @ X16 @ X17 @ X14)
% 0.20/0.57          | ~ (m1_subset_1 @ X18 @ X16)
% 0.20/0.57          | (r2_hidden @ (k4_tarski @ X19 @ X18) @ X17)
% 0.20/0.57          | ~ (r2_hidden @ (k4_tarski @ X19 @ X18) @ X14)
% 0.20/0.57          | ~ (m1_subset_1 @ X19 @ X15)
% 0.20/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_relset_1])).
% 0.20/0.57  thf('98', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.57          | ~ (m1_subset_1 @ X1 @ sk_A)
% 0.20/0.57          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ sk_B)
% 0.20/0.57          | (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.20/0.57          | ~ (m1_subset_1 @ X2 @ sk_A)
% 0.20/0.57          | ~ (r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['96', '97'])).
% 0.20/0.57  thf('99', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.57          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.57          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C)
% 0.20/0.57          | ~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_B)
% 0.20/0.57          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['95', '98'])).
% 0.20/0.57  thf('100', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)),
% 0.20/0.57      inference('clc', [status(thm)], ['62', '67'])).
% 0.20/0.57  thf('101', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.57          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C)
% 0.20/0.57          | ~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_B)
% 0.20/0.57          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.20/0.57      inference('demod', [status(thm)], ['99', '100'])).
% 0.20/0.57  thf('102', plain,
% 0.20/0.57      ((~ (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ sk_A)
% 0.20/0.57        | (r2_hidden @ 
% 0.20/0.57           (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.57            (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.57           sk_C)
% 0.20/0.57        | ~ (m1_subset_1 @ (sk_F @ sk_C @ sk_B @ sk_A @ sk_A) @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['94', '101'])).
% 0.20/0.57  thf('103', plain,
% 0.20/0.57      ((m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ sk_A)),
% 0.20/0.57      inference('clc', [status(thm)], ['75', '76'])).
% 0.20/0.57  thf('104', plain,
% 0.20/0.57      ((m1_subset_1 @ (sk_F @ sk_C @ sk_B @ sk_A @ sk_A) @ sk_A)),
% 0.20/0.57      inference('clc', [status(thm)], ['82', '83'])).
% 0.20/0.57  thf('105', plain,
% 0.20/0.57      ((r2_hidden @ 
% 0.20/0.57        (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.57         (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.57        sk_C)),
% 0.20/0.57      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.20/0.57  thf('106', plain, ($false), inference('demod', [status(thm)], ['93', '105'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
