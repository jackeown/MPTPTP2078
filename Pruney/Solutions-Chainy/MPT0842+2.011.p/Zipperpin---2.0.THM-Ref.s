%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H671i3zV3t

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 186 expanded)
%              Number of leaves         :   27 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  934 (3099 expanded)
%              Number of equality atoms :    7 (  15 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k8_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k10_relat_1 @ X19 @ X22 ) ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k10_relat_1 @ X6 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ X5 @ ( sk_D @ X6 @ X4 @ X5 ) ) @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X23: $i] :
      ( ~ ( m1_subset_1 @ X23 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X23 @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X23 @ sk_B ) )
   <= ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X23 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C ) )
   <= ( ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X23 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('20',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k10_relat_1 @ X6 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X6 @ X4 @ X5 ) @ X4 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('21',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k10_relat_1 @ X6 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X6 @ X4 @ X5 ) @ ( k2_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('26',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ ( k2_relat_1 @ sk_D_1 ) ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ ( k2_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X13 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('31',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('34',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(demod,[status(thm)],['31','34'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( m1_subset_1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
    | ~ ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X23 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','23','38'])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
   <= ( m1_subset_1 @ sk_F @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('41',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('42',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X23 @ sk_B ) )
   <= ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X23 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('44',plain,
    ( ( ~ ( r2_hidden @ sk_F @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ sk_C ) )
   <= ( ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X23 @ sk_B ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( m1_subset_1 @ sk_F @ sk_C )
   <= ( ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X23 @ sk_B ) )
      & ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
    | ~ ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X23 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F @ sk_C )
    | ~ ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
    | ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X23 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('48',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('49',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('50',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X3 ) @ X6 )
      | ~ ( r2_hidden @ X3 @ ( k2_relat_1 @ X6 ) )
      | ( r2_hidden @ X5 @ ( k10_relat_1 @ X6 @ X4 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_1 )
        | ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('54',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('55',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 )
      | ( r2_hidden @ X8 @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('56',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('58',plain,
    ( ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['52','53','58'])).

thf('60',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['49','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0 )
      = ( k10_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('62',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('63',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','39','46','47','48','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H671i3zV3t
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:20:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 73 iterations in 0.028s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.49  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(t53_relset_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( m1_subset_1 @
% 0.21/0.49                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.21/0.49                   ( ![E:$i]:
% 0.21/0.49                     ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.49                       ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.21/0.49                         ( ?[F:$i]:
% 0.21/0.49                           ( ( r2_hidden @ F @ B ) & 
% 0.21/0.49                             ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.21/0.49                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.49                  ( ![D:$i]:
% 0.21/0.49                    ( ( m1_subset_1 @
% 0.21/0.49                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.21/0.49                      ( ![E:$i]:
% 0.21/0.49                        ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.49                          ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.21/0.49                            ( ?[F:$i]:
% 0.21/0.49                              ( ( r2_hidden @ F @ B ) & 
% 0.21/0.49                                ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.21/0.49                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t53_relset_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)
% 0.21/0.49        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)) | 
% 0.21/0.49       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (((m1_subset_1 @ sk_F @ sk_C)
% 0.21/0.49        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (((m1_subset_1 @ sk_F @ sk_C)) | 
% 0.21/0.49       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['2'])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.21/0.49          | ((k8_relset_1 @ X20 @ X21 @ X19 @ X22) = (k10_relat_1 @ X19 @ X22)))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0)
% 0.21/0.49           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (((r2_hidden @ sk_F @ sk_B)
% 0.21/0.49        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))
% 0.21/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.21/0.49      inference('split', [status(esa)], ['7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.21/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['6', '8'])).
% 0.21/0.49  thf(t166_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ C ) =>
% 0.21/0.49       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.21/0.49         ( ?[D:$i]:
% 0.21/0.49           ( ( r2_hidden @ D @ B ) & 
% 0.21/0.49             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.21/0.49             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X5 @ (k10_relat_1 @ X6 @ X4))
% 0.21/0.49          | (r2_hidden @ (k4_tarski @ X5 @ (sk_D @ X6 @ X4 @ X5)) @ X6)
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (((~ (v1_relat_1 @ sk_D_1)
% 0.21/0.49         | (r2_hidden @ (k4_tarski @ sk_E @ (sk_D @ sk_D_1 @ sk_B @ sk_E)) @ 
% 0.21/0.49            sk_D_1)))
% 0.21/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(cc1_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( v1_relat_1 @ C ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         ((v1_relat_1 @ X10)
% 0.21/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.49  thf('14', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (((r2_hidden @ (k4_tarski @ sk_E @ (sk_D @ sk_D_1 @ sk_B @ sk_E)) @ 
% 0.21/0.49         sk_D_1))
% 0.21/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X23 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X23 @ sk_C)
% 0.21/0.49          | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.21/0.49          | ~ (r2_hidden @ X23 @ sk_B)
% 0.21/0.49          | ~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      ((![X23 : $i]:
% 0.21/0.49          (~ (m1_subset_1 @ X23 @ sk_C)
% 0.21/0.49           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.21/0.49           | ~ (r2_hidden @ X23 @ sk_B)))
% 0.21/0.49         <= ((![X23 : $i]:
% 0.21/0.49                (~ (m1_subset_1 @ X23 @ sk_C)
% 0.21/0.49                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.21/0.49                 | ~ (r2_hidden @ X23 @ sk_B))))),
% 0.21/0.49      inference('split', [status(esa)], ['16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (((~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B)
% 0.21/0.49         | ~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C)))
% 0.21/0.49         <= ((![X23 : $i]:
% 0.21/0.49                (~ (m1_subset_1 @ X23 @ sk_C)
% 0.21/0.49                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.21/0.49                 | ~ (r2_hidden @ X23 @ sk_B))) & 
% 0.21/0.49             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.21/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['6', '8'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X5 @ (k10_relat_1 @ X6 @ X4))
% 0.21/0.49          | (r2_hidden @ (sk_D @ X6 @ X4 @ X5) @ X4)
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (((~ (v1_relat_1 @ sk_D_1)
% 0.21/0.49         | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B)))
% 0.21/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B))
% 0.21/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.21/0.49      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.21/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['6', '8'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X5 @ (k10_relat_1 @ X6 @ X4))
% 0.21/0.49          | (r2_hidden @ (sk_D @ X6 @ X4 @ X5) @ (k2_relat_1 @ X6))
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (((~ (v1_relat_1 @ sk_D_1)
% 0.21/0.49         | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ (k2_relat_1 @ sk_D_1))))
% 0.21/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.49  thf('27', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ (k2_relat_1 @ sk_D_1)))
% 0.21/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.21/0.49      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_k2_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.49         ((m1_subset_1 @ (k2_relset_1 @ X13 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 0.21/0.49          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_C @ sk_D_1) @ 
% 0.21/0.49        (k1_zfmisc_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.49         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.21/0.49          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (((k2_relset_1 @ sk_A @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      ((m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['31', '34'])).
% 0.21/0.49  thf(t4_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.49       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.21/0.49          | (m1_subset_1 @ X0 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((m1_subset_1 @ X0 @ sk_C)
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C))
% 0.21/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['28', '37'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))) | 
% 0.21/0.49       ~
% 0.21/0.49       (![X23 : $i]:
% 0.21/0.49          (~ (m1_subset_1 @ X23 @ sk_C)
% 0.21/0.49           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.21/0.49           | ~ (r2_hidden @ X23 @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['18', '23', '38'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (((m1_subset_1 @ sk_F @ sk_C)) <= (((m1_subset_1 @ sk_F @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['2'])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['7'])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1))
% 0.21/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      ((![X23 : $i]:
% 0.21/0.49          (~ (m1_subset_1 @ X23 @ sk_C)
% 0.21/0.49           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.21/0.49           | ~ (r2_hidden @ X23 @ sk_B)))
% 0.21/0.49         <= ((![X23 : $i]:
% 0.21/0.49                (~ (m1_subset_1 @ X23 @ sk_C)
% 0.21/0.49                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.21/0.49                 | ~ (r2_hidden @ X23 @ sk_B))))),
% 0.21/0.49      inference('split', [status(esa)], ['16'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (((~ (r2_hidden @ sk_F @ sk_B) | ~ (m1_subset_1 @ sk_F @ sk_C)))
% 0.21/0.49         <= ((![X23 : $i]:
% 0.21/0.49                (~ (m1_subset_1 @ X23 @ sk_C)
% 0.21/0.49                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.21/0.49                 | ~ (r2_hidden @ X23 @ sk_B))) & 
% 0.21/0.49             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      ((~ (m1_subset_1 @ sk_F @ sk_C))
% 0.21/0.49         <= ((![X23 : $i]:
% 0.21/0.49                (~ (m1_subset_1 @ X23 @ sk_C)
% 0.21/0.49                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.21/0.49                 | ~ (r2_hidden @ X23 @ sk_B))) & 
% 0.21/0.49             ((r2_hidden @ sk_F @ sk_B)) & 
% 0.21/0.49             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['41', '44'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)) | 
% 0.21/0.49       ~
% 0.21/0.49       (![X23 : $i]:
% 0.21/0.49          (~ (m1_subset_1 @ X23 @ sk_C)
% 0.21/0.49           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.21/0.49           | ~ (r2_hidden @ X23 @ sk_B))) | 
% 0.21/0.49       ~ ((m1_subset_1 @ sk_F @ sk_C)) | ~ ((r2_hidden @ sk_F @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['40', '45'])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))) | 
% 0.21/0.49       (![X23 : $i]:
% 0.21/0.49          (~ (m1_subset_1 @ X23 @ sk_C)
% 0.21/0.49           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.21/0.49           | ~ (r2_hidden @ X23 @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['16'])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.21/0.49       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['7'])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['7'])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1))
% 0.21/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X3 @ X4)
% 0.21/0.49          | ~ (r2_hidden @ (k4_tarski @ X5 @ X3) @ X6)
% 0.21/0.49          | ~ (r2_hidden @ X3 @ (k2_relat_1 @ X6))
% 0.21/0.49          | (r2_hidden @ X5 @ (k10_relat_1 @ X6 @ X4))
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      ((![X0 : $i]:
% 0.21/0.49          (~ (v1_relat_1 @ sk_D_1)
% 0.21/0.49           | (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.21/0.49           | ~ (r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1))
% 0.21/0.49           | ~ (r2_hidden @ sk_F @ X0)))
% 0.21/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.49  thf('53', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1))
% 0.21/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf(t20_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ C ) =>
% 0.21/0.49       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.21/0.49         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.49           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9)
% 0.21/0.49          | (r2_hidden @ X8 @ (k2_relat_1 @ X9))
% 0.21/0.49          | ~ (v1_relat_1 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      (((~ (v1_relat_1 @ sk_D_1) | (r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1))))
% 0.21/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.49  thf('57', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      (((r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1)))
% 0.21/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      ((![X0 : $i]:
% 0.21/0.49          ((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.21/0.49           | ~ (r2_hidden @ sk_F @ X0)))
% 0.21/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['52', '53', '58'])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.21/0.49         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.21/0.49             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['49', '59'])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0)
% 0.21/0.49           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      ((~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))
% 0.21/0.49         <= (~
% 0.21/0.49             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.21/0.49      inference('split', [status(esa)], ['16'])).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      ((~ (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.21/0.49         <= (~
% 0.21/0.49             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 0.21/0.49       ~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)) | 
% 0.21/0.49       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['60', '63'])).
% 0.21/0.49  thf('65', plain, ($false),
% 0.21/0.49      inference('sat_resolution*', [status(thm)],
% 0.21/0.49                ['1', '3', '39', '46', '47', '48', '64'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
