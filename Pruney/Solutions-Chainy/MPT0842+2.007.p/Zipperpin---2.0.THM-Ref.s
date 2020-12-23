%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DEbhX5Yz8D

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:26 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 170 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  889 (2883 expanded)
%              Number of equality atoms :    8 (  20 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t53_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ~ ( v1_xboole_0 @ C )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ A )
                     => ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) )
                      <=> ? [F: $i] :
                            ( ( r2_hidden @ F @ B )
                            & ( r2_hidden @ ( k4_tarski @ E @ F ) @ D )
                            & ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ~ ( v1_xboole_0 @ C )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ A )
                       => ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) )
                        <=> ? [F: $i] :
                              ( ( r2_hidden @ F @ B )
                              & ( r2_hidden @ ( k4_tarski @ E @ F ) @ D )
                              & ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_relset_1])).

thf('0',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k8_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k10_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0 )
      = ( k10_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf(d14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i] :
      ( ( X14
       != ( k10_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ ( sk_E_1 @ X15 @ X11 @ X12 ) ) @ X12 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('11',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k10_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ ( sk_E_1 @ X15 @ X11 @ X12 ) ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) ) @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('24',plain,
    ( ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('26',plain,(
    ! [X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X25 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X25 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X25 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X25 @ sk_B ) )
   <= ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X25 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_C ) )
   <= ( ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X25 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X25 @ sk_B ) )
      & ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('30',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i] :
      ( ( X14
       != ( k10_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( sk_E_1 @ X15 @ X11 @ X12 ) @ X11 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('31',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k10_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( sk_E_1 @ X15 @ X11 @ X12 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1 ) @ sk_C )
   <= ( ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X25 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X25 @ sk_B ) )
      & ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
    | ~ ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X25 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
   <= ( m1_subset_1 @ sk_F @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('38',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('39',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X25 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X25 @ sk_B ) )
   <= ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X25 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference(split,[status(esa)],['26'])).

thf('41',plain,
    ( ( ~ ( r2_hidden @ sk_F @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ sk_C ) )
   <= ( ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X25 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X25 @ sk_B ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( m1_subset_1 @ sk_F @ sk_C )
   <= ( ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X25 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X25 @ sk_B ) )
      & ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 )
    | ~ ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X25 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X25 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F @ sk_C )
    | ~ ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
    | ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X25 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference(split,[status(esa)],['26'])).

thf('45',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('46',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('47',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,(
    ! [X11: $i,X12: $i,X14: $i,X16: $i,X17: $i] :
      ( ( X14
       != ( k10_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X12 )
      | ~ ( r2_hidden @ X17 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('49',plain,(
    ! [X11: $i,X12: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( r2_hidden @ X17 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X12 )
      | ( r2_hidden @ X16 @ ( k10_relat_1 @ X12 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 )
        | ~ ( v1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0 )
      = ( k10_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['26'])).

thf('56',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_1 )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','36','43','44','45','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DEbhX5Yz8D
% 0.13/0.37  % Computer   : n004.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 14:40:39 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.90/1.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.09  % Solved by: fo/fo7.sh
% 0.90/1.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.09  % done 370 iterations in 0.602s
% 0.90/1.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.09  % SZS output start Refutation
% 0.90/1.09  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.90/1.09  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.09  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.09  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.90/1.09  thf(sk_F_type, type, sk_F: $i).
% 0.90/1.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.09  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.09  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.90/1.09  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.90/1.09  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.09  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.90/1.09  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.90/1.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.09  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.09  thf(t53_relset_1, conjecture,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.90/1.09       ( ![B:$i]:
% 0.90/1.09         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.90/1.09           ( ![C:$i]:
% 0.90/1.09             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.90/1.09               ( ![D:$i]:
% 0.90/1.09                 ( ( m1_subset_1 @
% 0.90/1.09                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.90/1.09                   ( ![E:$i]:
% 0.90/1.09                     ( ( m1_subset_1 @ E @ A ) =>
% 0.90/1.09                       ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.90/1.09                         ( ?[F:$i]:
% 0.90/1.09                           ( ( r2_hidden @ F @ B ) & 
% 0.90/1.09                             ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.90/1.09                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.09  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.09    (~( ![A:$i]:
% 0.90/1.09        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.90/1.09          ( ![B:$i]:
% 0.90/1.09            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.90/1.09              ( ![C:$i]:
% 0.90/1.09                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.90/1.09                  ( ![D:$i]:
% 0.90/1.09                    ( ( m1_subset_1 @
% 0.90/1.09                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.90/1.09                      ( ![E:$i]:
% 0.90/1.09                        ( ( m1_subset_1 @ E @ A ) =>
% 0.90/1.09                          ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.90/1.09                            ( ?[F:$i]:
% 0.90/1.09                              ( ( r2_hidden @ F @ B ) & 
% 0.90/1.09                                ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.90/1.09                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.90/1.09    inference('cnf.neg', [status(esa)], [t53_relset_1])).
% 0.90/1.09  thf('0', plain,
% 0.90/1.09      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1)
% 0.90/1.09        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('1', plain,
% 0.90/1.09      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1)) | 
% 0.90/1.09       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.90/1.09      inference('split', [status(esa)], ['0'])).
% 0.90/1.09  thf('2', plain,
% 0.90/1.09      (((m1_subset_1 @ sk_F @ sk_C)
% 0.90/1.09        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('3', plain,
% 0.90/1.09      (((m1_subset_1 @ sk_F @ sk_C)) | 
% 0.90/1.09       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.90/1.09      inference('split', [status(esa)], ['2'])).
% 0.90/1.09  thf('4', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(redefinition_k8_relset_1, axiom,
% 0.90/1.09    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.09       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.90/1.09  thf('5', plain,
% 0.90/1.09      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.90/1.09          | ((k8_relset_1 @ X22 @ X23 @ X21 @ X24) = (k10_relat_1 @ X21 @ X24)))),
% 0.90/1.09      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.90/1.09  thf('6', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0)
% 0.90/1.09           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['4', '5'])).
% 0.90/1.09  thf('7', plain,
% 0.90/1.09      (((r2_hidden @ sk_F @ sk_B)
% 0.90/1.09        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('8', plain,
% 0.90/1.09      (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))
% 0.90/1.09         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.09      inference('split', [status(esa)], ['7'])).
% 0.90/1.09  thf('9', plain,
% 0.90/1.09      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.90/1.09         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.09      inference('sup+', [status(thm)], ['6', '8'])).
% 0.90/1.09  thf(d14_relat_1, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( v1_relat_1 @ A ) =>
% 0.90/1.09       ( ![B:$i,C:$i]:
% 0.90/1.09         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.90/1.09           ( ![D:$i]:
% 0.90/1.09             ( ( r2_hidden @ D @ C ) <=>
% 0.90/1.09               ( ?[E:$i]:
% 0.90/1.09                 ( ( r2_hidden @ E @ B ) & 
% 0.90/1.09                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.90/1.09  thf('10', plain,
% 0.90/1.09      (![X11 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 0.90/1.09         (((X14) != (k10_relat_1 @ X12 @ X11))
% 0.90/1.09          | (r2_hidden @ (k4_tarski @ X15 @ (sk_E_1 @ X15 @ X11 @ X12)) @ X12)
% 0.90/1.09          | ~ (r2_hidden @ X15 @ X14)
% 0.90/1.09          | ~ (v1_relat_1 @ X12))),
% 0.90/1.09      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.90/1.09  thf('11', plain,
% 0.90/1.09      (![X11 : $i, X12 : $i, X15 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X12)
% 0.90/1.09          | ~ (r2_hidden @ X15 @ (k10_relat_1 @ X12 @ X11))
% 0.90/1.09          | (r2_hidden @ (k4_tarski @ X15 @ (sk_E_1 @ X15 @ X11 @ X12)) @ X12))),
% 0.90/1.09      inference('simplify', [status(thm)], ['10'])).
% 0.90/1.09  thf('12', plain,
% 0.90/1.09      ((((r2_hidden @ 
% 0.90/1.09          (k4_tarski @ sk_E_2 @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1)) @ sk_D_1)
% 0.90/1.09         | ~ (v1_relat_1 @ sk_D_1)))
% 0.90/1.09         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['9', '11'])).
% 0.90/1.09  thf('13', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(cc1_relset_1, axiom,
% 0.90/1.09    (![A:$i,B:$i,C:$i]:
% 0.90/1.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.09       ( v1_relat_1 @ C ) ))).
% 0.90/1.09  thf('14', plain,
% 0.90/1.09      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.90/1.09         ((v1_relat_1 @ X18)
% 0.90/1.09          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.90/1.09      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.90/1.09  thf('15', plain, ((v1_relat_1 @ sk_D_1)),
% 0.90/1.09      inference('sup-', [status(thm)], ['13', '14'])).
% 0.90/1.09  thf('16', plain,
% 0.90/1.09      (((r2_hidden @ 
% 0.90/1.09         (k4_tarski @ sk_E_2 @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1)) @ sk_D_1))
% 0.90/1.09         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.09      inference('demod', [status(thm)], ['12', '15'])).
% 0.90/1.09  thf('17', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(l3_subset_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.09       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.90/1.09  thf('18', plain,
% 0.90/1.09      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.90/1.09         (~ (r2_hidden @ X5 @ X6)
% 0.90/1.09          | (r2_hidden @ X5 @ X7)
% 0.90/1.09          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.90/1.09      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.90/1.09  thf('19', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_C))
% 0.90/1.09          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.09  thf('20', plain,
% 0.90/1.09      (((r2_hidden @ 
% 0.90/1.09         (k4_tarski @ sk_E_2 @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1)) @ 
% 0.90/1.09         (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.90/1.09         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['16', '19'])).
% 0.90/1.09  thf(l54_zfmisc_1, axiom,
% 0.90/1.09    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.09     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.90/1.09       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.90/1.09  thf('21', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.09         ((r2_hidden @ X2 @ X3)
% 0.90/1.09          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.90/1.09      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.90/1.09  thf('22', plain,
% 0.90/1.09      (((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1) @ sk_C))
% 0.90/1.09         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['20', '21'])).
% 0.90/1.09  thf(t1_subset, axiom,
% 0.90/1.09    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.90/1.09  thf('23', plain,
% 0.90/1.09      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.90/1.09      inference('cnf', [status(esa)], [t1_subset])).
% 0.90/1.09  thf('24', plain,
% 0.90/1.09      (((m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1) @ sk_C))
% 0.90/1.09         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['22', '23'])).
% 0.90/1.09  thf('25', plain,
% 0.90/1.09      (((r2_hidden @ 
% 0.90/1.09         (k4_tarski @ sk_E_2 @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1)) @ sk_D_1))
% 0.90/1.09         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.09      inference('demod', [status(thm)], ['12', '15'])).
% 0.90/1.09  thf('26', plain,
% 0.90/1.09      (![X25 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.09          | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X25) @ sk_D_1)
% 0.90/1.09          | ~ (r2_hidden @ X25 @ sk_B)
% 0.90/1.09          | ~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('27', plain,
% 0.90/1.09      ((![X25 : $i]:
% 0.90/1.09          (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.09           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X25) @ sk_D_1)
% 0.90/1.09           | ~ (r2_hidden @ X25 @ sk_B)))
% 0.90/1.09         <= ((![X25 : $i]:
% 0.90/1.09                (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.09                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X25) @ sk_D_1)
% 0.90/1.09                 | ~ (r2_hidden @ X25 @ sk_B))))),
% 0.90/1.09      inference('split', [status(esa)], ['26'])).
% 0.90/1.09  thf('28', plain,
% 0.90/1.09      (((~ (r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1) @ sk_B)
% 0.90/1.09         | ~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1) @ sk_C)))
% 0.90/1.09         <= ((![X25 : $i]:
% 0.90/1.09                (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.09                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X25) @ sk_D_1)
% 0.90/1.09                 | ~ (r2_hidden @ X25 @ sk_B))) & 
% 0.90/1.09             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['25', '27'])).
% 0.90/1.09  thf('29', plain,
% 0.90/1.09      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.90/1.09         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.09      inference('sup+', [status(thm)], ['6', '8'])).
% 0.90/1.09  thf('30', plain,
% 0.90/1.09      (![X11 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 0.90/1.09         (((X14) != (k10_relat_1 @ X12 @ X11))
% 0.90/1.09          | (r2_hidden @ (sk_E_1 @ X15 @ X11 @ X12) @ X11)
% 0.90/1.09          | ~ (r2_hidden @ X15 @ X14)
% 0.90/1.09          | ~ (v1_relat_1 @ X12))),
% 0.90/1.09      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.90/1.09  thf('31', plain,
% 0.90/1.09      (![X11 : $i, X12 : $i, X15 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X12)
% 0.90/1.09          | ~ (r2_hidden @ X15 @ (k10_relat_1 @ X12 @ X11))
% 0.90/1.09          | (r2_hidden @ (sk_E_1 @ X15 @ X11 @ X12) @ X11))),
% 0.90/1.09      inference('simplify', [status(thm)], ['30'])).
% 0.90/1.09  thf('32', plain,
% 0.90/1.09      ((((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1) @ sk_B)
% 0.90/1.09         | ~ (v1_relat_1 @ sk_D_1)))
% 0.90/1.09         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['29', '31'])).
% 0.90/1.09  thf('33', plain, ((v1_relat_1 @ sk_D_1)),
% 0.90/1.09      inference('sup-', [status(thm)], ['13', '14'])).
% 0.90/1.09  thf('34', plain,
% 0.90/1.09      (((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1) @ sk_B))
% 0.90/1.09         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.09      inference('demod', [status(thm)], ['32', '33'])).
% 0.90/1.09  thf('35', plain,
% 0.90/1.09      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_B @ sk_D_1) @ sk_C))
% 0.90/1.09         <= ((![X25 : $i]:
% 0.90/1.09                (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.09                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X25) @ sk_D_1)
% 0.90/1.09                 | ~ (r2_hidden @ X25 @ sk_B))) & 
% 0.90/1.09             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.09      inference('demod', [status(thm)], ['28', '34'])).
% 0.90/1.09  thf('36', plain,
% 0.90/1.09      (~ ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))) | 
% 0.90/1.09       ~
% 0.90/1.09       (![X25 : $i]:
% 0.90/1.09          (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.09           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X25) @ sk_D_1)
% 0.90/1.09           | ~ (r2_hidden @ X25 @ sk_B)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['24', '35'])).
% 0.90/1.09  thf('37', plain,
% 0.90/1.09      (((m1_subset_1 @ sk_F @ sk_C)) <= (((m1_subset_1 @ sk_F @ sk_C)))),
% 0.90/1.09      inference('split', [status(esa)], ['2'])).
% 0.90/1.09  thf('38', plain,
% 0.90/1.09      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.90/1.09      inference('split', [status(esa)], ['7'])).
% 0.90/1.09  thf('39', plain,
% 0.90/1.09      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1))
% 0.90/1.09         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1)))),
% 0.90/1.09      inference('split', [status(esa)], ['0'])).
% 0.90/1.09  thf('40', plain,
% 0.90/1.09      ((![X25 : $i]:
% 0.90/1.09          (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.09           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X25) @ sk_D_1)
% 0.90/1.09           | ~ (r2_hidden @ X25 @ sk_B)))
% 0.90/1.09         <= ((![X25 : $i]:
% 0.90/1.09                (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.09                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X25) @ sk_D_1)
% 0.90/1.09                 | ~ (r2_hidden @ X25 @ sk_B))))),
% 0.90/1.09      inference('split', [status(esa)], ['26'])).
% 0.90/1.09  thf('41', plain,
% 0.90/1.09      (((~ (r2_hidden @ sk_F @ sk_B) | ~ (m1_subset_1 @ sk_F @ sk_C)))
% 0.90/1.09         <= ((![X25 : $i]:
% 0.90/1.09                (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.09                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X25) @ sk_D_1)
% 0.90/1.09                 | ~ (r2_hidden @ X25 @ sk_B))) & 
% 0.90/1.09             ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['39', '40'])).
% 0.90/1.09  thf('42', plain,
% 0.90/1.09      ((~ (m1_subset_1 @ sk_F @ sk_C))
% 0.90/1.09         <= ((![X25 : $i]:
% 0.90/1.09                (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.09                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X25) @ sk_D_1)
% 0.90/1.09                 | ~ (r2_hidden @ X25 @ sk_B))) & 
% 0.90/1.09             ((r2_hidden @ sk_F @ sk_B)) & 
% 0.90/1.09             ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['38', '41'])).
% 0.90/1.09  thf('43', plain,
% 0.90/1.09      (~ ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1)) | 
% 0.90/1.09       ~
% 0.90/1.09       (![X25 : $i]:
% 0.90/1.09          (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.09           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X25) @ sk_D_1)
% 0.90/1.09           | ~ (r2_hidden @ X25 @ sk_B))) | 
% 0.90/1.09       ~ ((m1_subset_1 @ sk_F @ sk_C)) | ~ ((r2_hidden @ sk_F @ sk_B))),
% 0.90/1.09      inference('sup-', [status(thm)], ['37', '42'])).
% 0.90/1.09  thf('44', plain,
% 0.90/1.09      (~ ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))) | 
% 0.90/1.09       (![X25 : $i]:
% 0.90/1.09          (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.09           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X25) @ sk_D_1)
% 0.90/1.09           | ~ (r2_hidden @ X25 @ sk_B)))),
% 0.90/1.09      inference('split', [status(esa)], ['26'])).
% 0.90/1.09  thf('45', plain,
% 0.90/1.09      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.90/1.09       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.90/1.09      inference('split', [status(esa)], ['7'])).
% 0.90/1.09  thf('46', plain,
% 0.90/1.09      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.90/1.09      inference('split', [status(esa)], ['7'])).
% 0.90/1.09  thf('47', plain,
% 0.90/1.09      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1))
% 0.90/1.09         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1)))),
% 0.90/1.09      inference('split', [status(esa)], ['0'])).
% 0.90/1.09  thf('48', plain,
% 0.90/1.09      (![X11 : $i, X12 : $i, X14 : $i, X16 : $i, X17 : $i]:
% 0.90/1.09         (((X14) != (k10_relat_1 @ X12 @ X11))
% 0.90/1.09          | (r2_hidden @ X16 @ X14)
% 0.90/1.09          | ~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X12)
% 0.90/1.09          | ~ (r2_hidden @ X17 @ X11)
% 0.90/1.09          | ~ (v1_relat_1 @ X12))),
% 0.90/1.09      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.90/1.09  thf('49', plain,
% 0.90/1.09      (![X11 : $i, X12 : $i, X16 : $i, X17 : $i]:
% 0.90/1.09         (~ (v1_relat_1 @ X12)
% 0.90/1.09          | ~ (r2_hidden @ X17 @ X11)
% 0.90/1.09          | ~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X12)
% 0.90/1.09          | (r2_hidden @ X16 @ (k10_relat_1 @ X12 @ X11)))),
% 0.90/1.09      inference('simplify', [status(thm)], ['48'])).
% 0.90/1.09  thf('50', plain,
% 0.90/1.09      ((![X0 : $i]:
% 0.90/1.09          ((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.90/1.09           | ~ (r2_hidden @ sk_F @ X0)
% 0.90/1.09           | ~ (v1_relat_1 @ sk_D_1)))
% 0.90/1.09         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['47', '49'])).
% 0.90/1.09  thf('51', plain, ((v1_relat_1 @ sk_D_1)),
% 0.90/1.09      inference('sup-', [status(thm)], ['13', '14'])).
% 0.90/1.09  thf('52', plain,
% 0.90/1.09      ((![X0 : $i]:
% 0.90/1.09          ((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.90/1.09           | ~ (r2_hidden @ sk_F @ X0)))
% 0.90/1.09         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1)))),
% 0.90/1.09      inference('demod', [status(thm)], ['50', '51'])).
% 0.90/1.09  thf('53', plain,
% 0.90/1.09      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.90/1.09         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.90/1.09             ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['46', '52'])).
% 0.90/1.09  thf('54', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0)
% 0.90/1.09           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['4', '5'])).
% 0.90/1.09  thf('55', plain,
% 0.90/1.09      ((~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))
% 0.90/1.09         <= (~
% 0.90/1.09             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.09      inference('split', [status(esa)], ['26'])).
% 0.90/1.09  thf('56', plain,
% 0.90/1.09      ((~ (r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.90/1.09         <= (~
% 0.90/1.09             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['54', '55'])).
% 0.90/1.09  thf('57', plain,
% 0.90/1.09      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 0.90/1.09       ~ ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_1)) | 
% 0.90/1.09       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['53', '56'])).
% 0.90/1.09  thf('58', plain, ($false),
% 0.90/1.09      inference('sat_resolution*', [status(thm)],
% 0.90/1.09                ['1', '3', '36', '43', '44', '45', '57'])).
% 0.90/1.09  
% 0.90/1.09  % SZS output end Refutation
% 0.90/1.09  
% 0.90/1.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
