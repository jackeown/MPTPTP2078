%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NLbfSBlBG7

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:28 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 182 expanded)
%              Number of leaves         :   26 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  810 (2796 expanded)
%              Number of equality atoms :    7 (  20 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

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
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k8_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k10_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ X0 )
      = ( k10_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k10_relat_1 @ X25 @ X23 ) )
      | ( r2_hidden @ ( k4_tarski @ X24 @ ( sk_D_2 @ X25 @ X23 @ X24 ) ) @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('9',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_3 )
      | ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) ) @ sk_D_3 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
    | ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) ) @ sk_D_3 )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('17',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ sk_C_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X30 ) @ sk_D_3 )
      | ~ ( r2_hidden @ X30 @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ X0 )
      = ( k10_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('19',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ sk_C_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X30 ) @ sk_D_3 )
      | ~ ( r2_hidden @ X30 @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X0 ) @ sk_D_3 )
        | ~ ( m1_subset_1 @ X0 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 )
      | ~ ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k10_relat_1 @ X25 @ X23 ) )
      | ( r2_hidden @ ( sk_D_2 @ X25 @ X23 @ X24 ) @ X23 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('24',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_3 )
      | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['12','13'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_B )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) ) @ sk_D_3 )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( m1_subset_1 @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('36',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('41',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('42',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r2_hidden @ ( k4_tarski @ X24 @ X22 ) @ X25 )
      | ~ ( r2_hidden @ X22 @ ( k2_relat_1 @ X25 ) )
      | ( r2_hidden @ X24 @ ( k10_relat_1 @ X25 @ X23 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_3 )
        | ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_3 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['12','13'])).

thf('46',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ),
    inference(split,[status(esa)],['0'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('47',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 )
      | ( r2_hidden @ X14 @ X16 )
      | ( X16
       != ( k2_relat_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('48',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ ( k2_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_3 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ),
    inference(demod,[status(thm)],['44','45','49'])).

thf('51',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ X0 )
      = ( k10_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('53',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ sk_C_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X30 ) @ sk_D_3 )
      | ~ ( r2_hidden @ X30 @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['51','55'])).

thf('57',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NLbfSBlBG7
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:06:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.36/1.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.36/1.55  % Solved by: fo/fo7.sh
% 1.36/1.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.36/1.55  % done 728 iterations in 1.081s
% 1.36/1.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.36/1.55  % SZS output start Refutation
% 1.36/1.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.36/1.55  thf(sk_F_type, type, sk_F: $i).
% 1.36/1.55  thf(sk_E_type, type, sk_E: $i).
% 1.36/1.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.36/1.55  thf(sk_B_type, type, sk_B: $i).
% 1.36/1.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.36/1.55  thf(sk_D_3_type, type, sk_D_3: $i).
% 1.36/1.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.36/1.55  thf(sk_A_type, type, sk_A: $i).
% 1.36/1.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.36/1.55  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.36/1.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.36/1.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.36/1.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.36/1.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.36/1.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.36/1.55  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 1.36/1.55  thf(t53_relset_1, conjecture,
% 1.36/1.55    (![A:$i]:
% 1.36/1.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.36/1.55       ( ![B:$i]:
% 1.36/1.55         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.36/1.55           ( ![C:$i]:
% 1.36/1.55             ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.36/1.55               ( ![D:$i]:
% 1.36/1.55                 ( ( m1_subset_1 @
% 1.36/1.55                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.36/1.55                   ( ![E:$i]:
% 1.36/1.55                     ( ( m1_subset_1 @ E @ A ) =>
% 1.36/1.55                       ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 1.36/1.55                         ( ?[F:$i]:
% 1.36/1.55                           ( ( r2_hidden @ F @ B ) & 
% 1.36/1.55                             ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 1.36/1.55                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.36/1.55  thf(zf_stmt_0, negated_conjecture,
% 1.36/1.55    (~( ![A:$i]:
% 1.36/1.55        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.36/1.55          ( ![B:$i]:
% 1.36/1.55            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.36/1.55              ( ![C:$i]:
% 1.36/1.55                ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.36/1.55                  ( ![D:$i]:
% 1.36/1.55                    ( ( m1_subset_1 @
% 1.36/1.55                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 1.36/1.55                      ( ![E:$i]:
% 1.36/1.55                        ( ( m1_subset_1 @ E @ A ) =>
% 1.36/1.55                          ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 1.36/1.55                            ( ?[F:$i]:
% 1.36/1.55                              ( ( r2_hidden @ F @ B ) & 
% 1.36/1.55                                ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 1.36/1.55                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.36/1.55    inference('cnf.neg', [status(esa)], [t53_relset_1])).
% 1.36/1.55  thf('0', plain,
% 1.36/1.55      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)
% 1.36/1.55        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 1.36/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.55  thf('1', plain,
% 1.36/1.55      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)) | 
% 1.36/1.55       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 1.36/1.55      inference('split', [status(esa)], ['0'])).
% 1.36/1.55  thf('2', plain,
% 1.36/1.55      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.36/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.55  thf(redefinition_k8_relset_1, axiom,
% 1.36/1.55    (![A:$i,B:$i,C:$i,D:$i]:
% 1.36/1.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.36/1.55       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 1.36/1.55  thf('3', plain,
% 1.36/1.55      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.36/1.55         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.36/1.55          | ((k8_relset_1 @ X27 @ X28 @ X26 @ X29) = (k10_relat_1 @ X26 @ X29)))),
% 1.36/1.55      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.36/1.55  thf('4', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         ((k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ X0)
% 1.36/1.55           = (k10_relat_1 @ sk_D_3 @ X0))),
% 1.36/1.55      inference('sup-', [status(thm)], ['2', '3'])).
% 1.36/1.55  thf('5', plain,
% 1.36/1.55      (((r2_hidden @ sk_F @ sk_B)
% 1.36/1.55        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 1.36/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.55  thf('6', plain,
% 1.36/1.55      (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))
% 1.36/1.55         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 1.36/1.55      inference('split', [status(esa)], ['5'])).
% 1.36/1.55  thf('7', plain,
% 1.36/1.55      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ sk_B)))
% 1.36/1.55         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 1.36/1.55      inference('sup+', [status(thm)], ['4', '6'])).
% 1.36/1.55  thf(t166_relat_1, axiom,
% 1.36/1.55    (![A:$i,B:$i,C:$i]:
% 1.36/1.55     ( ( v1_relat_1 @ C ) =>
% 1.36/1.55       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 1.36/1.55         ( ?[D:$i]:
% 1.36/1.55           ( ( r2_hidden @ D @ B ) & 
% 1.36/1.55             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 1.36/1.55             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 1.36/1.55  thf('8', plain,
% 1.36/1.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.36/1.55         (~ (r2_hidden @ X24 @ (k10_relat_1 @ X25 @ X23))
% 1.36/1.55          | (r2_hidden @ (k4_tarski @ X24 @ (sk_D_2 @ X25 @ X23 @ X24)) @ X25)
% 1.36/1.55          | ~ (v1_relat_1 @ X25))),
% 1.36/1.55      inference('cnf', [status(esa)], [t166_relat_1])).
% 1.36/1.55  thf('9', plain,
% 1.36/1.55      (((~ (v1_relat_1 @ sk_D_3)
% 1.36/1.55         | (r2_hidden @ (k4_tarski @ sk_E @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E)) @ 
% 1.36/1.55            sk_D_3)))
% 1.36/1.55         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 1.36/1.55      inference('sup-', [status(thm)], ['7', '8'])).
% 1.36/1.55  thf('10', plain,
% 1.36/1.55      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.36/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.55  thf(cc2_relat_1, axiom,
% 1.36/1.55    (![A:$i]:
% 1.36/1.55     ( ( v1_relat_1 @ A ) =>
% 1.36/1.55       ( ![B:$i]:
% 1.36/1.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.36/1.55  thf('11', plain,
% 1.36/1.55      (![X11 : $i, X12 : $i]:
% 1.36/1.55         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 1.36/1.55          | (v1_relat_1 @ X11)
% 1.36/1.55          | ~ (v1_relat_1 @ X12))),
% 1.36/1.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.36/1.55  thf('12', plain,
% 1.36/1.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)) | (v1_relat_1 @ sk_D_3))),
% 1.36/1.55      inference('sup-', [status(thm)], ['10', '11'])).
% 1.36/1.55  thf(fc6_relat_1, axiom,
% 1.36/1.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.36/1.55  thf('13', plain,
% 1.36/1.55      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 1.36/1.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.36/1.55  thf('14', plain, ((v1_relat_1 @ sk_D_3)),
% 1.36/1.55      inference('demod', [status(thm)], ['12', '13'])).
% 1.36/1.55  thf('15', plain,
% 1.36/1.55      (((r2_hidden @ (k4_tarski @ sk_E @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E)) @ 
% 1.36/1.55         sk_D_3))
% 1.36/1.55         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 1.36/1.55      inference('demod', [status(thm)], ['9', '14'])).
% 1.36/1.55  thf('16', plain,
% 1.36/1.55      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ sk_B)))
% 1.36/1.55         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 1.36/1.55      inference('sup+', [status(thm)], ['4', '6'])).
% 1.36/1.55  thf('17', plain,
% 1.36/1.55      (![X30 : $i]:
% 1.36/1.55         (~ (m1_subset_1 @ X30 @ sk_C_1)
% 1.36/1.55          | ~ (r2_hidden @ (k4_tarski @ sk_E @ X30) @ sk_D_3)
% 1.36/1.55          | ~ (r2_hidden @ X30 @ sk_B)
% 1.36/1.55          | ~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 1.36/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.55  thf('18', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         ((k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ X0)
% 1.36/1.55           = (k10_relat_1 @ sk_D_3 @ X0))),
% 1.36/1.55      inference('sup-', [status(thm)], ['2', '3'])).
% 1.36/1.55  thf('19', plain,
% 1.36/1.55      (![X30 : $i]:
% 1.36/1.55         (~ (m1_subset_1 @ X30 @ sk_C_1)
% 1.36/1.55          | ~ (r2_hidden @ (k4_tarski @ sk_E @ X30) @ sk_D_3)
% 1.36/1.55          | ~ (r2_hidden @ X30 @ sk_B)
% 1.36/1.55          | ~ (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ sk_B)))),
% 1.36/1.55      inference('demod', [status(thm)], ['17', '18'])).
% 1.36/1.55  thf('20', plain,
% 1.36/1.55      ((![X0 : $i]:
% 1.36/1.55          (~ (r2_hidden @ X0 @ sk_B)
% 1.36/1.55           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X0) @ sk_D_3)
% 1.36/1.55           | ~ (m1_subset_1 @ X0 @ sk_C_1)))
% 1.36/1.55         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 1.36/1.55      inference('sup-', [status(thm)], ['16', '19'])).
% 1.36/1.55  thf('21', plain,
% 1.36/1.55      (((~ (m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1)
% 1.36/1.55         | ~ (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_B)))
% 1.36/1.55         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 1.36/1.55      inference('sup-', [status(thm)], ['15', '20'])).
% 1.36/1.55  thf('22', plain,
% 1.36/1.55      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ sk_B)))
% 1.36/1.55         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 1.36/1.55      inference('sup+', [status(thm)], ['4', '6'])).
% 1.36/1.55  thf('23', plain,
% 1.36/1.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.36/1.55         (~ (r2_hidden @ X24 @ (k10_relat_1 @ X25 @ X23))
% 1.36/1.55          | (r2_hidden @ (sk_D_2 @ X25 @ X23 @ X24) @ X23)
% 1.36/1.55          | ~ (v1_relat_1 @ X25))),
% 1.36/1.55      inference('cnf', [status(esa)], [t166_relat_1])).
% 1.36/1.55  thf('24', plain,
% 1.36/1.55      (((~ (v1_relat_1 @ sk_D_3)
% 1.36/1.55         | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_B)))
% 1.36/1.55         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 1.36/1.55      inference('sup-', [status(thm)], ['22', '23'])).
% 1.36/1.55  thf('25', plain, ((v1_relat_1 @ sk_D_3)),
% 1.36/1.55      inference('demod', [status(thm)], ['12', '13'])).
% 1.36/1.55  thf('26', plain,
% 1.36/1.55      (((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_B))
% 1.36/1.55         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 1.36/1.55      inference('demod', [status(thm)], ['24', '25'])).
% 1.36/1.55  thf('27', plain,
% 1.36/1.55      ((~ (m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1))
% 1.36/1.55         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 1.36/1.55      inference('demod', [status(thm)], ['21', '26'])).
% 1.36/1.55  thf('28', plain,
% 1.36/1.55      (((r2_hidden @ (k4_tarski @ sk_E @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E)) @ 
% 1.36/1.55         sk_D_3))
% 1.36/1.55         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 1.36/1.55      inference('demod', [status(thm)], ['9', '14'])).
% 1.36/1.55  thf('29', plain,
% 1.36/1.55      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.36/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.55  thf(l3_subset_1, axiom,
% 1.36/1.55    (![A:$i,B:$i]:
% 1.36/1.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.36/1.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.36/1.55  thf('30', plain,
% 1.36/1.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.36/1.55         (~ (r2_hidden @ X8 @ X9)
% 1.36/1.55          | (r2_hidden @ X8 @ X10)
% 1.36/1.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.36/1.55      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.36/1.55  thf('31', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))
% 1.36/1.55          | ~ (r2_hidden @ X0 @ sk_D_3))),
% 1.36/1.55      inference('sup-', [status(thm)], ['29', '30'])).
% 1.36/1.55  thf('32', plain,
% 1.36/1.55      (((r2_hidden @ (k4_tarski @ sk_E @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E)) @ 
% 1.36/1.55         (k2_zfmisc_1 @ sk_A @ sk_C_1)))
% 1.36/1.55         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 1.36/1.55      inference('sup-', [status(thm)], ['28', '31'])).
% 1.36/1.55  thf(l54_zfmisc_1, axiom,
% 1.36/1.55    (![A:$i,B:$i,C:$i,D:$i]:
% 1.36/1.55     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 1.36/1.55       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 1.36/1.55  thf('33', plain,
% 1.36/1.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.36/1.55         ((r2_hidden @ X2 @ X3)
% 1.36/1.55          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 1.36/1.55      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.36/1.55  thf('34', plain,
% 1.36/1.55      (((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1))
% 1.36/1.55         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 1.36/1.55      inference('sup-', [status(thm)], ['32', '33'])).
% 1.36/1.55  thf(d2_subset_1, axiom,
% 1.36/1.55    (![A:$i,B:$i]:
% 1.36/1.55     ( ( ( v1_xboole_0 @ A ) =>
% 1.36/1.55         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.36/1.55       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.36/1.55         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.36/1.55  thf('35', plain,
% 1.36/1.55      (![X5 : $i, X6 : $i]:
% 1.36/1.55         (~ (r2_hidden @ X5 @ X6)
% 1.36/1.55          | (m1_subset_1 @ X5 @ X6)
% 1.36/1.55          | (v1_xboole_0 @ X6))),
% 1.36/1.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.36/1.55  thf('36', plain,
% 1.36/1.55      ((((v1_xboole_0 @ sk_C_1)
% 1.36/1.55         | (m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1)))
% 1.36/1.55         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 1.36/1.55      inference('sup-', [status(thm)], ['34', '35'])).
% 1.36/1.55  thf('37', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 1.36/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.55  thf('38', plain,
% 1.36/1.55      (((m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1))
% 1.36/1.55         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 1.36/1.55      inference('clc', [status(thm)], ['36', '37'])).
% 1.36/1.55  thf('39', plain,
% 1.36/1.55      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 1.36/1.55      inference('demod', [status(thm)], ['27', '38'])).
% 1.36/1.55  thf('40', plain,
% 1.36/1.55      (((r2_hidden @ sk_F @ sk_B)) | 
% 1.36/1.55       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 1.36/1.55      inference('split', [status(esa)], ['5'])).
% 1.36/1.55  thf('41', plain,
% 1.36/1.55      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 1.36/1.55      inference('split', [status(esa)], ['5'])).
% 1.36/1.55  thf('42', plain,
% 1.36/1.55      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3))
% 1.36/1.55         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 1.36/1.55      inference('split', [status(esa)], ['0'])).
% 1.36/1.55  thf('43', plain,
% 1.36/1.55      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.36/1.55         (~ (r2_hidden @ X22 @ X23)
% 1.36/1.55          | ~ (r2_hidden @ (k4_tarski @ X24 @ X22) @ X25)
% 1.36/1.55          | ~ (r2_hidden @ X22 @ (k2_relat_1 @ X25))
% 1.36/1.55          | (r2_hidden @ X24 @ (k10_relat_1 @ X25 @ X23))
% 1.36/1.55          | ~ (v1_relat_1 @ X25))),
% 1.36/1.55      inference('cnf', [status(esa)], [t166_relat_1])).
% 1.36/1.55  thf('44', plain,
% 1.36/1.55      ((![X0 : $i]:
% 1.36/1.55          (~ (v1_relat_1 @ sk_D_3)
% 1.36/1.55           | (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ X0))
% 1.36/1.55           | ~ (r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_3))
% 1.36/1.55           | ~ (r2_hidden @ sk_F @ X0)))
% 1.36/1.55         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 1.36/1.55      inference('sup-', [status(thm)], ['42', '43'])).
% 1.36/1.55  thf('45', plain, ((v1_relat_1 @ sk_D_3)),
% 1.36/1.55      inference('demod', [status(thm)], ['12', '13'])).
% 1.36/1.55  thf('46', plain,
% 1.36/1.55      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3))
% 1.36/1.55         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 1.36/1.55      inference('split', [status(esa)], ['0'])).
% 1.36/1.55  thf(d5_relat_1, axiom,
% 1.36/1.55    (![A:$i,B:$i]:
% 1.36/1.55     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.36/1.55       ( ![C:$i]:
% 1.36/1.55         ( ( r2_hidden @ C @ B ) <=>
% 1.36/1.55           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 1.36/1.55  thf('47', plain,
% 1.36/1.55      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.36/1.55         (~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15)
% 1.36/1.55          | (r2_hidden @ X14 @ X16)
% 1.36/1.55          | ((X16) != (k2_relat_1 @ X15)))),
% 1.36/1.55      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.36/1.55  thf('48', plain,
% 1.36/1.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.36/1.55         ((r2_hidden @ X14 @ (k2_relat_1 @ X15))
% 1.36/1.55          | ~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15))),
% 1.36/1.55      inference('simplify', [status(thm)], ['47'])).
% 1.36/1.55  thf('49', plain,
% 1.36/1.55      (((r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_3)))
% 1.36/1.55         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 1.36/1.55      inference('sup-', [status(thm)], ['46', '48'])).
% 1.36/1.55  thf('50', plain,
% 1.36/1.55      ((![X0 : $i]:
% 1.36/1.55          ((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ X0))
% 1.36/1.55           | ~ (r2_hidden @ sk_F @ X0)))
% 1.36/1.55         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 1.36/1.55      inference('demod', [status(thm)], ['44', '45', '49'])).
% 1.36/1.55  thf('51', plain,
% 1.36/1.55      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ sk_B)))
% 1.36/1.55         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 1.36/1.55             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 1.36/1.55      inference('sup-', [status(thm)], ['41', '50'])).
% 1.36/1.55  thf('52', plain,
% 1.36/1.55      (![X0 : $i]:
% 1.36/1.55         ((k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ X0)
% 1.36/1.55           = (k10_relat_1 @ sk_D_3 @ X0))),
% 1.36/1.55      inference('sup-', [status(thm)], ['2', '3'])).
% 1.36/1.55  thf('53', plain,
% 1.36/1.55      (![X30 : $i]:
% 1.36/1.55         (~ (m1_subset_1 @ X30 @ sk_C_1)
% 1.36/1.55          | ~ (r2_hidden @ (k4_tarski @ sk_E @ X30) @ sk_D_3)
% 1.36/1.55          | ~ (r2_hidden @ X30 @ sk_B)
% 1.36/1.55          | ~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 1.36/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.55  thf('54', plain,
% 1.36/1.55      ((~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))
% 1.36/1.55         <= (~
% 1.36/1.55             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 1.36/1.55      inference('split', [status(esa)], ['53'])).
% 1.36/1.55  thf('55', plain,
% 1.36/1.55      ((~ (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ sk_B)))
% 1.36/1.55         <= (~
% 1.36/1.55             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 1.36/1.55      inference('sup-', [status(thm)], ['52', '54'])).
% 1.36/1.55  thf('56', plain,
% 1.36/1.55      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 1.36/1.55       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))) | 
% 1.36/1.55       ~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3))),
% 1.36/1.55      inference('sup-', [status(thm)], ['51', '55'])).
% 1.36/1.55  thf('57', plain, ($false),
% 1.36/1.55      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '56'])).
% 1.36/1.55  
% 1.36/1.55  % SZS output end Refutation
% 1.36/1.55  
% 1.36/1.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
