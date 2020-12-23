%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eUkrQNV1vQ

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:26 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 183 expanded)
%              Number of leaves         :   26 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  921 (3066 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

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
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k8_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k10_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0 )
      = ( k10_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k10_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( sk_D @ X13 @ X11 @ X12 ) ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) ) @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('21',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('23',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('25',plain,(
    ! [X24: $i] :
      ( ~ ( m1_subset_1 @ X24 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X24 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X24 @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X24 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X24 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C ) )
   <= ( ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X24 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X24 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('29',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k10_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( sk_D @ X13 @ X11 @ X12 ) @ X11 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('30',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('32',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C )
   <= ( ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X24 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X24 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
    | ~ ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X24 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','33'])).

thf('35',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
   <= ( m1_subset_1 @ sk_F @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('36',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('37',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X24 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) )
   <= ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X24 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(split,[status(esa)],['25'])).

thf('39',plain,
    ( ( ~ ( r2_hidden @ sk_F @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ sk_C ) )
   <= ( ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X24 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X24 @ sk_B ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( m1_subset_1 @ sk_F @ sk_C )
   <= ( ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X24 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X24 @ sk_B ) )
      & ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
    | ~ ! [X24: $i] :
          ( ~ ( m1_subset_1 @ X24 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X24 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X24 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F @ sk_C )
    | ~ ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
    | ! [X24: $i] :
        ( ~ ( m1_subset_1 @ X24 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X24 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(split,[status(esa)],['25'])).

thf('43',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('44',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('45',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X10 ) @ X13 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X13 ) )
      | ( r2_hidden @ X12 @ ( k10_relat_1 @ X13 @ X11 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_1 )
        | ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('51',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X16 )
      | ( r2_hidden @ X15 @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('52',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('54',plain,
    ( ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('56',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['44','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0 )
      = ( k10_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['25'])).

thf('59',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','34','41','42','43','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eUkrQNV1vQ
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:47:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.37/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.60  % Solved by: fo/fo7.sh
% 0.37/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.60  % done 387 iterations in 0.126s
% 0.37/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.60  % SZS output start Refutation
% 0.37/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.60  thf(sk_E_type, type, sk_E: $i).
% 0.37/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.60  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.60  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.37/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.37/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.60  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.37/0.60  thf(sk_F_type, type, sk_F: $i).
% 0.37/0.60  thf(t53_relset_1, conjecture,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.60       ( ![B:$i]:
% 0.37/0.60         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.37/0.60           ( ![C:$i]:
% 0.37/0.60             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.37/0.60               ( ![D:$i]:
% 0.37/0.60                 ( ( m1_subset_1 @
% 0.37/0.60                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.37/0.60                   ( ![E:$i]:
% 0.37/0.60                     ( ( m1_subset_1 @ E @ A ) =>
% 0.37/0.60                       ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.37/0.60                         ( ?[F:$i]:
% 0.37/0.60                           ( ( r2_hidden @ F @ B ) & 
% 0.37/0.60                             ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.37/0.60                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.60    (~( ![A:$i]:
% 0.37/0.60        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.60          ( ![B:$i]:
% 0.37/0.60            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.37/0.60              ( ![C:$i]:
% 0.37/0.60                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.37/0.60                  ( ![D:$i]:
% 0.37/0.60                    ( ( m1_subset_1 @
% 0.37/0.60                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.37/0.60                      ( ![E:$i]:
% 0.37/0.60                        ( ( m1_subset_1 @ E @ A ) =>
% 0.37/0.60                          ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.37/0.60                            ( ?[F:$i]:
% 0.37/0.60                              ( ( r2_hidden @ F @ B ) & 
% 0.37/0.60                                ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.37/0.60                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.37/0.60    inference('cnf.neg', [status(esa)], [t53_relset_1])).
% 0.37/0.60  thf('0', plain,
% 0.37/0.60      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)
% 0.37/0.60        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('1', plain,
% 0.37/0.60      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)) | 
% 0.37/0.60       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.37/0.60      inference('split', [status(esa)], ['0'])).
% 0.37/0.60  thf('2', plain,
% 0.37/0.60      (((m1_subset_1 @ sk_F @ sk_C)
% 0.37/0.60        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('3', plain,
% 0.37/0.60      (((m1_subset_1 @ sk_F @ sk_C)) | 
% 0.37/0.60       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.37/0.60      inference('split', [status(esa)], ['2'])).
% 0.37/0.60  thf('4', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(redefinition_k8_relset_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.60       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.37/0.60  thf('5', plain,
% 0.37/0.60      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.60         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.37/0.60          | ((k8_relset_1 @ X21 @ X22 @ X20 @ X23) = (k10_relat_1 @ X20 @ X23)))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.37/0.60  thf('6', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0)
% 0.37/0.60           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.60  thf('7', plain,
% 0.37/0.60      (((r2_hidden @ sk_F @ sk_B)
% 0.37/0.60        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('8', plain,
% 0.37/0.60      (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))
% 0.37/0.60         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.37/0.60      inference('split', [status(esa)], ['7'])).
% 0.37/0.60  thf('9', plain,
% 0.37/0.60      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.37/0.60         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.37/0.60      inference('sup+', [status(thm)], ['6', '8'])).
% 0.37/0.60  thf(t166_relat_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( v1_relat_1 @ C ) =>
% 0.37/0.60       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.37/0.60         ( ?[D:$i]:
% 0.37/0.60           ( ( r2_hidden @ D @ B ) & 
% 0.37/0.60             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.37/0.60             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.37/0.60  thf('10', plain,
% 0.37/0.60      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X12 @ (k10_relat_1 @ X13 @ X11))
% 0.37/0.60          | (r2_hidden @ (k4_tarski @ X12 @ (sk_D @ X13 @ X11 @ X12)) @ X13)
% 0.37/0.60          | ~ (v1_relat_1 @ X13))),
% 0.37/0.60      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.37/0.60  thf('11', plain,
% 0.37/0.60      (((~ (v1_relat_1 @ sk_D_1)
% 0.37/0.60         | (r2_hidden @ (k4_tarski @ sk_E @ (sk_D @ sk_D_1 @ sk_B @ sk_E)) @ 
% 0.37/0.60            sk_D_1)))
% 0.37/0.60         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.60  thf('12', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(cc1_relset_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.60       ( v1_relat_1 @ C ) ))).
% 0.37/0.60  thf('13', plain,
% 0.37/0.60      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.60         ((v1_relat_1 @ X17)
% 0.37/0.60          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.37/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.60  thf('14', plain, ((v1_relat_1 @ sk_D_1)),
% 0.37/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.60  thf('15', plain,
% 0.37/0.60      (((r2_hidden @ (k4_tarski @ sk_E @ (sk_D @ sk_D_1 @ sk_B @ sk_E)) @ 
% 0.37/0.60         sk_D_1))
% 0.37/0.60         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.37/0.60      inference('demod', [status(thm)], ['11', '14'])).
% 0.37/0.60  thf('16', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(l3_subset_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.37/0.60  thf('17', plain,
% 0.37/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X5 @ X6)
% 0.37/0.60          | (r2_hidden @ X5 @ X7)
% 0.37/0.60          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.37/0.60      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.37/0.60  thf('18', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_C))
% 0.37/0.60          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.37/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.60  thf('19', plain,
% 0.37/0.60      (((r2_hidden @ (k4_tarski @ sk_E @ (sk_D @ sk_D_1 @ sk_B @ sk_E)) @ 
% 0.37/0.60         (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.37/0.60         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['15', '18'])).
% 0.37/0.60  thf(l54_zfmisc_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.60     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.37/0.60       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.37/0.60  thf('20', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.60         ((r2_hidden @ X2 @ X3)
% 0.37/0.60          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.37/0.60      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.37/0.60  thf('21', plain,
% 0.37/0.60      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C))
% 0.37/0.60         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.60  thf(t1_subset, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.37/0.60  thf('22', plain,
% 0.37/0.60      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.37/0.60      inference('cnf', [status(esa)], [t1_subset])).
% 0.37/0.60  thf('23', plain,
% 0.37/0.60      (((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C))
% 0.37/0.60         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.60  thf('24', plain,
% 0.37/0.60      (((r2_hidden @ (k4_tarski @ sk_E @ (sk_D @ sk_D_1 @ sk_B @ sk_E)) @ 
% 0.37/0.60         sk_D_1))
% 0.37/0.60         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.37/0.60      inference('demod', [status(thm)], ['11', '14'])).
% 0.37/0.60  thf('25', plain,
% 0.37/0.60      (![X24 : $i]:
% 0.37/0.60         (~ (m1_subset_1 @ X24 @ sk_C)
% 0.37/0.60          | ~ (r2_hidden @ (k4_tarski @ sk_E @ X24) @ sk_D_1)
% 0.37/0.60          | ~ (r2_hidden @ X24 @ sk_B)
% 0.37/0.60          | ~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('26', plain,
% 0.37/0.60      ((![X24 : $i]:
% 0.37/0.60          (~ (m1_subset_1 @ X24 @ sk_C)
% 0.37/0.60           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X24) @ sk_D_1)
% 0.37/0.60           | ~ (r2_hidden @ X24 @ sk_B)))
% 0.37/0.60         <= ((![X24 : $i]:
% 0.37/0.60                (~ (m1_subset_1 @ X24 @ sk_C)
% 0.37/0.60                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X24) @ sk_D_1)
% 0.37/0.60                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 0.37/0.60      inference('split', [status(esa)], ['25'])).
% 0.37/0.60  thf('27', plain,
% 0.37/0.60      (((~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B)
% 0.37/0.60         | ~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C)))
% 0.37/0.60         <= ((![X24 : $i]:
% 0.37/0.60                (~ (m1_subset_1 @ X24 @ sk_C)
% 0.37/0.60                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X24) @ sk_D_1)
% 0.37/0.60                 | ~ (r2_hidden @ X24 @ sk_B))) & 
% 0.37/0.60             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['24', '26'])).
% 0.37/0.60  thf('28', plain,
% 0.37/0.60      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.37/0.60         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.37/0.60      inference('sup+', [status(thm)], ['6', '8'])).
% 0.37/0.60  thf('29', plain,
% 0.37/0.60      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X12 @ (k10_relat_1 @ X13 @ X11))
% 0.37/0.60          | (r2_hidden @ (sk_D @ X13 @ X11 @ X12) @ X11)
% 0.37/0.60          | ~ (v1_relat_1 @ X13))),
% 0.37/0.60      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.37/0.60  thf('30', plain,
% 0.37/0.60      (((~ (v1_relat_1 @ sk_D_1)
% 0.37/0.60         | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B)))
% 0.37/0.60         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.60  thf('31', plain, ((v1_relat_1 @ sk_D_1)),
% 0.37/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.60  thf('32', plain,
% 0.37/0.60      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B))
% 0.37/0.60         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.37/0.60      inference('demod', [status(thm)], ['30', '31'])).
% 0.37/0.60  thf('33', plain,
% 0.37/0.60      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C))
% 0.37/0.60         <= ((![X24 : $i]:
% 0.37/0.60                (~ (m1_subset_1 @ X24 @ sk_C)
% 0.37/0.60                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X24) @ sk_D_1)
% 0.37/0.60                 | ~ (r2_hidden @ X24 @ sk_B))) & 
% 0.37/0.60             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.37/0.60      inference('demod', [status(thm)], ['27', '32'])).
% 0.37/0.60  thf('34', plain,
% 0.37/0.60      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))) | 
% 0.37/0.60       ~
% 0.37/0.60       (![X24 : $i]:
% 0.37/0.60          (~ (m1_subset_1 @ X24 @ sk_C)
% 0.37/0.60           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X24) @ sk_D_1)
% 0.37/0.60           | ~ (r2_hidden @ X24 @ sk_B)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['23', '33'])).
% 0.37/0.60  thf('35', plain,
% 0.37/0.60      (((m1_subset_1 @ sk_F @ sk_C)) <= (((m1_subset_1 @ sk_F @ sk_C)))),
% 0.37/0.60      inference('split', [status(esa)], ['2'])).
% 0.37/0.60  thf('36', plain,
% 0.37/0.60      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.37/0.60      inference('split', [status(esa)], ['7'])).
% 0.37/0.60  thf('37', plain,
% 0.37/0.60      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1))
% 0.37/0.60         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.37/0.60      inference('split', [status(esa)], ['0'])).
% 0.37/0.60  thf('38', plain,
% 0.37/0.60      ((![X24 : $i]:
% 0.37/0.60          (~ (m1_subset_1 @ X24 @ sk_C)
% 0.37/0.60           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X24) @ sk_D_1)
% 0.37/0.60           | ~ (r2_hidden @ X24 @ sk_B)))
% 0.37/0.60         <= ((![X24 : $i]:
% 0.37/0.60                (~ (m1_subset_1 @ X24 @ sk_C)
% 0.37/0.60                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X24) @ sk_D_1)
% 0.37/0.60                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 0.37/0.60      inference('split', [status(esa)], ['25'])).
% 0.37/0.60  thf('39', plain,
% 0.37/0.60      (((~ (r2_hidden @ sk_F @ sk_B) | ~ (m1_subset_1 @ sk_F @ sk_C)))
% 0.37/0.60         <= ((![X24 : $i]:
% 0.37/0.60                (~ (m1_subset_1 @ X24 @ sk_C)
% 0.37/0.60                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X24) @ sk_D_1)
% 0.37/0.60                 | ~ (r2_hidden @ X24 @ sk_B))) & 
% 0.37/0.60             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.60  thf('40', plain,
% 0.37/0.60      ((~ (m1_subset_1 @ sk_F @ sk_C))
% 0.37/0.60         <= ((![X24 : $i]:
% 0.37/0.60                (~ (m1_subset_1 @ X24 @ sk_C)
% 0.37/0.60                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X24) @ sk_D_1)
% 0.37/0.60                 | ~ (r2_hidden @ X24 @ sk_B))) & 
% 0.37/0.60             ((r2_hidden @ sk_F @ sk_B)) & 
% 0.37/0.60             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['36', '39'])).
% 0.37/0.60  thf('41', plain,
% 0.37/0.60      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)) | 
% 0.37/0.60       ~
% 0.37/0.60       (![X24 : $i]:
% 0.37/0.60          (~ (m1_subset_1 @ X24 @ sk_C)
% 0.37/0.60           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X24) @ sk_D_1)
% 0.37/0.60           | ~ (r2_hidden @ X24 @ sk_B))) | 
% 0.37/0.60       ~ ((m1_subset_1 @ sk_F @ sk_C)) | ~ ((r2_hidden @ sk_F @ sk_B))),
% 0.37/0.60      inference('sup-', [status(thm)], ['35', '40'])).
% 0.37/0.60  thf('42', plain,
% 0.37/0.60      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))) | 
% 0.37/0.60       (![X24 : $i]:
% 0.37/0.60          (~ (m1_subset_1 @ X24 @ sk_C)
% 0.37/0.60           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X24) @ sk_D_1)
% 0.37/0.60           | ~ (r2_hidden @ X24 @ sk_B)))),
% 0.37/0.60      inference('split', [status(esa)], ['25'])).
% 0.37/0.60  thf('43', plain,
% 0.37/0.60      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.37/0.60       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.37/0.60      inference('split', [status(esa)], ['7'])).
% 0.37/0.60  thf('44', plain,
% 0.37/0.60      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.37/0.60      inference('split', [status(esa)], ['7'])).
% 0.37/0.60  thf('45', plain,
% 0.37/0.60      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1))
% 0.37/0.60         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.37/0.60      inference('split', [status(esa)], ['0'])).
% 0.37/0.60  thf('46', plain,
% 0.37/0.60      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X10 @ X11)
% 0.37/0.60          | ~ (r2_hidden @ (k4_tarski @ X12 @ X10) @ X13)
% 0.37/0.60          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X13))
% 0.37/0.60          | (r2_hidden @ X12 @ (k10_relat_1 @ X13 @ X11))
% 0.37/0.60          | ~ (v1_relat_1 @ X13))),
% 0.37/0.60      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.37/0.60  thf('47', plain,
% 0.37/0.60      ((![X0 : $i]:
% 0.37/0.60          (~ (v1_relat_1 @ sk_D_1)
% 0.37/0.60           | (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.37/0.60           | ~ (r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1))
% 0.37/0.60           | ~ (r2_hidden @ sk_F @ X0)))
% 0.37/0.60         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.60  thf('48', plain, ((v1_relat_1 @ sk_D_1)),
% 0.37/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.60  thf('49', plain,
% 0.37/0.60      ((![X0 : $i]:
% 0.37/0.60          ((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.37/0.60           | ~ (r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1))
% 0.37/0.60           | ~ (r2_hidden @ sk_F @ X0)))
% 0.37/0.60         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.37/0.60      inference('demod', [status(thm)], ['47', '48'])).
% 0.37/0.60  thf('50', plain,
% 0.37/0.60      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1))
% 0.37/0.60         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.37/0.60      inference('split', [status(esa)], ['0'])).
% 0.37/0.60  thf(t20_relat_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( v1_relat_1 @ C ) =>
% 0.37/0.60       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.37/0.60         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.37/0.60           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.37/0.60  thf('51', plain,
% 0.37/0.60      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.60         (~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X16)
% 0.37/0.60          | (r2_hidden @ X15 @ (k2_relat_1 @ X16))
% 0.37/0.60          | ~ (v1_relat_1 @ X16))),
% 0.37/0.60      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.37/0.60  thf('52', plain,
% 0.37/0.60      (((~ (v1_relat_1 @ sk_D_1) | (r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1))))
% 0.37/0.60         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.60  thf('53', plain, ((v1_relat_1 @ sk_D_1)),
% 0.37/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.60  thf('54', plain,
% 0.37/0.60      (((r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1)))
% 0.37/0.60         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.37/0.60      inference('demod', [status(thm)], ['52', '53'])).
% 0.37/0.60  thf('55', plain,
% 0.37/0.60      ((![X0 : $i]:
% 0.37/0.60          ((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.37/0.60           | ~ (r2_hidden @ sk_F @ X0)))
% 0.37/0.60         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.37/0.60      inference('demod', [status(thm)], ['49', '54'])).
% 0.37/0.60  thf('56', plain,
% 0.37/0.60      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.37/0.60         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.37/0.60             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['44', '55'])).
% 0.37/0.60  thf('57', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0)
% 0.37/0.60           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.60  thf('58', plain,
% 0.37/0.60      ((~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))
% 0.37/0.60         <= (~
% 0.37/0.60             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.37/0.60      inference('split', [status(esa)], ['25'])).
% 0.37/0.60  thf('59', plain,
% 0.37/0.60      ((~ (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.37/0.60         <= (~
% 0.37/0.60             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['57', '58'])).
% 0.37/0.60  thf('60', plain,
% 0.37/0.60      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 0.37/0.60       ~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)) | 
% 0.37/0.60       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['56', '59'])).
% 0.37/0.60  thf('61', plain, ($false),
% 0.37/0.60      inference('sat_resolution*', [status(thm)],
% 0.37/0.60                ['1', '3', '34', '41', '42', '43', '60'])).
% 0.37/0.60  
% 0.37/0.60  % SZS output end Refutation
% 0.37/0.60  
% 0.37/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
