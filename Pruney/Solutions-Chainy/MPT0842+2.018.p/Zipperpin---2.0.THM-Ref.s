%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HcMoMcT57t

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:27 EST 2020

% Result     : Theorem 2.42s
% Output     : Refutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 175 expanded)
%              Number of leaves         :   26 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  786 (2675 expanded)
%              Number of equality atoms :    7 (  20 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k8_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k10_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0 )
      = ( k10_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k10_relat_1 @ X26 @ X24 ) )
      | ( r2_hidden @ ( k4_tarski @ X25 @ ( sk_D_1 @ X26 @ X24 @ X25 ) ) @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('9',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) ) @ sk_D_2 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
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
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) ) @ sk_D_2 )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('17',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X31 ) @ sk_D_2 )
      | ~ ( r2_hidden @ X31 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0 )
      = ( k10_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('19',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X31 ) @ sk_D_2 )
      | ~ ( r2_hidden @ X31 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X0 ) @ sk_D_2 )
        | ~ ( m1_subset_1 @ X0 @ sk_C ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('23',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k10_relat_1 @ X26 @ X24 ) )
      | ( r2_hidden @ ( sk_D_1 @ X26 @ X24 @ X25 ) @ X24 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('24',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['12','13'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) ) @ sk_D_2 )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
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
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
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
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
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
    ( ( ( v1_xboole_0 @ sk_C )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('41',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('42',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

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

thf('43',plain,(
    ! [X14: $i,X15: $i,X17: $i,X19: $i,X20: $i] :
      ( ( X17
       != ( k10_relat_1 @ X15 @ X14 ) )
      | ( r2_hidden @ X19 @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X20 ) @ X15 )
      | ~ ( r2_hidden @ X20 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('44',plain,(
    ! [X14: $i,X15: $i,X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( r2_hidden @ X20 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X20 ) @ X15 )
      | ( r2_hidden @ X19 @ ( k10_relat_1 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 )
        | ~ ( v1_relat_1 @ sk_D_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['12','13'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0 )
      = ( k10_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('50',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X31 ) @ sk_D_2 )
      | ~ ( r2_hidden @ X31 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HcMoMcT57t
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.42/2.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.42/2.61  % Solved by: fo/fo7.sh
% 2.42/2.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.42/2.61  % done 957 iterations in 2.162s
% 2.42/2.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.42/2.61  % SZS output start Refutation
% 2.42/2.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.42/2.61  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.42/2.61  thf(sk_C_type, type, sk_C: $i).
% 2.42/2.61  thf(sk_E_2_type, type, sk_E_2: $i).
% 2.42/2.61  thf(sk_B_type, type, sk_B: $i).
% 2.42/2.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.42/2.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.42/2.61  thf(sk_A_type, type, sk_A: $i).
% 2.42/2.61  thf(sk_F_type, type, sk_F: $i).
% 2.42/2.61  thf(sk_D_2_type, type, sk_D_2: $i).
% 2.42/2.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.42/2.61  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 2.42/2.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.42/2.61  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 2.42/2.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.42/2.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.42/2.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.42/2.61  thf(t53_relset_1, conjecture,
% 2.42/2.61    (![A:$i]:
% 2.42/2.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.42/2.61       ( ![B:$i]:
% 2.42/2.61         ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.42/2.61           ( ![C:$i]:
% 2.42/2.61             ( ( ~( v1_xboole_0 @ C ) ) =>
% 2.42/2.61               ( ![D:$i]:
% 2.42/2.61                 ( ( m1_subset_1 @
% 2.42/2.61                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 2.42/2.61                   ( ![E:$i]:
% 2.42/2.61                     ( ( m1_subset_1 @ E @ A ) =>
% 2.42/2.61                       ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 2.42/2.61                         ( ?[F:$i]:
% 2.42/2.61                           ( ( r2_hidden @ F @ B ) & 
% 2.42/2.61                             ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 2.42/2.61                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.42/2.61  thf(zf_stmt_0, negated_conjecture,
% 2.42/2.61    (~( ![A:$i]:
% 2.42/2.61        ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.42/2.61          ( ![B:$i]:
% 2.42/2.61            ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.42/2.61              ( ![C:$i]:
% 2.42/2.61                ( ( ~( v1_xboole_0 @ C ) ) =>
% 2.42/2.61                  ( ![D:$i]:
% 2.42/2.61                    ( ( m1_subset_1 @
% 2.42/2.61                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 2.42/2.61                      ( ![E:$i]:
% 2.42/2.61                        ( ( m1_subset_1 @ E @ A ) =>
% 2.42/2.61                          ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 2.42/2.61                            ( ?[F:$i]:
% 2.42/2.61                              ( ( r2_hidden @ F @ B ) & 
% 2.42/2.61                                ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 2.42/2.61                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 2.42/2.61    inference('cnf.neg', [status(esa)], [t53_relset_1])).
% 2.42/2.61  thf('0', plain,
% 2.42/2.61      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)
% 2.42/2.61        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 2.42/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.61  thf('1', plain,
% 2.42/2.61      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)) | 
% 2.42/2.61       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 2.42/2.61      inference('split', [status(esa)], ['0'])).
% 2.42/2.61  thf('2', plain,
% 2.42/2.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.42/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.61  thf(redefinition_k8_relset_1, axiom,
% 2.42/2.61    (![A:$i,B:$i,C:$i,D:$i]:
% 2.42/2.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.42/2.61       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 2.42/2.61  thf('3', plain,
% 2.42/2.61      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 2.42/2.61         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 2.42/2.61          | ((k8_relset_1 @ X28 @ X29 @ X27 @ X30) = (k10_relat_1 @ X27 @ X30)))),
% 2.42/2.61      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 2.42/2.61  thf('4', plain,
% 2.42/2.61      (![X0 : $i]:
% 2.42/2.61         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0)
% 2.42/2.61           = (k10_relat_1 @ sk_D_2 @ X0))),
% 2.42/2.61      inference('sup-', [status(thm)], ['2', '3'])).
% 2.42/2.61  thf('5', plain,
% 2.42/2.61      (((r2_hidden @ sk_F @ sk_B)
% 2.42/2.61        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 2.42/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.61  thf('6', plain,
% 2.42/2.61      (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))
% 2.42/2.61         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 2.42/2.61      inference('split', [status(esa)], ['5'])).
% 2.42/2.61  thf('7', plain,
% 2.42/2.61      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 2.42/2.61         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 2.42/2.61      inference('sup+', [status(thm)], ['4', '6'])).
% 2.42/2.61  thf(t166_relat_1, axiom,
% 2.42/2.61    (![A:$i,B:$i,C:$i]:
% 2.42/2.61     ( ( v1_relat_1 @ C ) =>
% 2.42/2.61       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 2.42/2.61         ( ?[D:$i]:
% 2.42/2.61           ( ( r2_hidden @ D @ B ) & 
% 2.42/2.61             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 2.42/2.61             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 2.42/2.61  thf('8', plain,
% 2.42/2.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.42/2.61         (~ (r2_hidden @ X25 @ (k10_relat_1 @ X26 @ X24))
% 2.42/2.61          | (r2_hidden @ (k4_tarski @ X25 @ (sk_D_1 @ X26 @ X24 @ X25)) @ X26)
% 2.42/2.61          | ~ (v1_relat_1 @ X26))),
% 2.42/2.61      inference('cnf', [status(esa)], [t166_relat_1])).
% 2.42/2.61  thf('9', plain,
% 2.42/2.61      (((~ (v1_relat_1 @ sk_D_2)
% 2.42/2.61         | (r2_hidden @ 
% 2.42/2.61            (k4_tarski @ sk_E_2 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2)) @ sk_D_2)))
% 2.42/2.61         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 2.42/2.61      inference('sup-', [status(thm)], ['7', '8'])).
% 2.42/2.61  thf('10', plain,
% 2.42/2.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.42/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.61  thf(cc2_relat_1, axiom,
% 2.42/2.61    (![A:$i]:
% 2.42/2.61     ( ( v1_relat_1 @ A ) =>
% 2.42/2.61       ( ![B:$i]:
% 2.42/2.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.42/2.61  thf('11', plain,
% 2.42/2.61      (![X11 : $i, X12 : $i]:
% 2.42/2.61         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 2.42/2.61          | (v1_relat_1 @ X11)
% 2.42/2.61          | ~ (v1_relat_1 @ X12))),
% 2.42/2.61      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.42/2.61  thf('12', plain,
% 2.42/2.61      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_D_2))),
% 2.42/2.61      inference('sup-', [status(thm)], ['10', '11'])).
% 2.42/2.61  thf(fc6_relat_1, axiom,
% 2.42/2.61    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.42/2.61  thf('13', plain,
% 2.42/2.61      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 2.42/2.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.42/2.61  thf('14', plain, ((v1_relat_1 @ sk_D_2)),
% 2.42/2.61      inference('demod', [status(thm)], ['12', '13'])).
% 2.42/2.61  thf('15', plain,
% 2.42/2.61      (((r2_hidden @ 
% 2.42/2.61         (k4_tarski @ sk_E_2 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2)) @ sk_D_2))
% 2.42/2.61         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 2.42/2.61      inference('demod', [status(thm)], ['9', '14'])).
% 2.42/2.61  thf('16', plain,
% 2.42/2.61      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 2.42/2.61         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 2.42/2.61      inference('sup+', [status(thm)], ['4', '6'])).
% 2.42/2.61  thf('17', plain,
% 2.42/2.61      (![X31 : $i]:
% 2.42/2.61         (~ (m1_subset_1 @ X31 @ sk_C)
% 2.42/2.61          | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X31) @ sk_D_2)
% 2.42/2.61          | ~ (r2_hidden @ X31 @ sk_B)
% 2.42/2.61          | ~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 2.42/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.61  thf('18', plain,
% 2.42/2.61      (![X0 : $i]:
% 2.42/2.61         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0)
% 2.42/2.61           = (k10_relat_1 @ sk_D_2 @ X0))),
% 2.42/2.61      inference('sup-', [status(thm)], ['2', '3'])).
% 2.42/2.61  thf('19', plain,
% 2.42/2.61      (![X31 : $i]:
% 2.42/2.61         (~ (m1_subset_1 @ X31 @ sk_C)
% 2.42/2.61          | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X31) @ sk_D_2)
% 2.42/2.61          | ~ (r2_hidden @ X31 @ sk_B)
% 2.42/2.61          | ~ (r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))),
% 2.42/2.61      inference('demod', [status(thm)], ['17', '18'])).
% 2.42/2.61  thf('20', plain,
% 2.42/2.61      ((![X0 : $i]:
% 2.42/2.61          (~ (r2_hidden @ X0 @ sk_B)
% 2.42/2.61           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X0) @ sk_D_2)
% 2.42/2.61           | ~ (m1_subset_1 @ X0 @ sk_C)))
% 2.42/2.61         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 2.42/2.61      inference('sup-', [status(thm)], ['16', '19'])).
% 2.42/2.61  thf('21', plain,
% 2.42/2.61      (((~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C)
% 2.42/2.61         | ~ (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B)))
% 2.42/2.61         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 2.42/2.61      inference('sup-', [status(thm)], ['15', '20'])).
% 2.42/2.61  thf('22', plain,
% 2.42/2.61      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 2.42/2.61         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 2.42/2.61      inference('sup+', [status(thm)], ['4', '6'])).
% 2.42/2.61  thf('23', plain,
% 2.42/2.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.42/2.61         (~ (r2_hidden @ X25 @ (k10_relat_1 @ X26 @ X24))
% 2.42/2.61          | (r2_hidden @ (sk_D_1 @ X26 @ X24 @ X25) @ X24)
% 2.42/2.61          | ~ (v1_relat_1 @ X26))),
% 2.42/2.61      inference('cnf', [status(esa)], [t166_relat_1])).
% 2.42/2.61  thf('24', plain,
% 2.42/2.61      (((~ (v1_relat_1 @ sk_D_2)
% 2.42/2.61         | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B)))
% 2.42/2.61         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 2.42/2.61      inference('sup-', [status(thm)], ['22', '23'])).
% 2.42/2.61  thf('25', plain, ((v1_relat_1 @ sk_D_2)),
% 2.42/2.61      inference('demod', [status(thm)], ['12', '13'])).
% 2.42/2.61  thf('26', plain,
% 2.42/2.61      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B))
% 2.42/2.61         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 2.42/2.61      inference('demod', [status(thm)], ['24', '25'])).
% 2.42/2.61  thf('27', plain,
% 2.42/2.61      ((~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C))
% 2.42/2.61         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 2.42/2.61      inference('demod', [status(thm)], ['21', '26'])).
% 2.42/2.61  thf('28', plain,
% 2.42/2.61      (((r2_hidden @ 
% 2.42/2.61         (k4_tarski @ sk_E_2 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2)) @ sk_D_2))
% 2.42/2.61         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 2.42/2.61      inference('demod', [status(thm)], ['9', '14'])).
% 2.42/2.61  thf('29', plain,
% 2.42/2.61      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.42/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.61  thf(l3_subset_1, axiom,
% 2.42/2.61    (![A:$i,B:$i]:
% 2.42/2.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.42/2.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 2.42/2.61  thf('30', plain,
% 2.42/2.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.42/2.61         (~ (r2_hidden @ X8 @ X9)
% 2.42/2.61          | (r2_hidden @ X8 @ X10)
% 2.42/2.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 2.42/2.61      inference('cnf', [status(esa)], [l3_subset_1])).
% 2.42/2.61  thf('31', plain,
% 2.42/2.61      (![X0 : $i]:
% 2.42/2.61         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_C))
% 2.42/2.61          | ~ (r2_hidden @ X0 @ sk_D_2))),
% 2.42/2.61      inference('sup-', [status(thm)], ['29', '30'])).
% 2.42/2.61  thf('32', plain,
% 2.42/2.61      (((r2_hidden @ 
% 2.42/2.61         (k4_tarski @ sk_E_2 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2)) @ 
% 2.42/2.61         (k2_zfmisc_1 @ sk_A @ sk_C)))
% 2.42/2.61         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 2.42/2.61      inference('sup-', [status(thm)], ['28', '31'])).
% 2.42/2.61  thf(l54_zfmisc_1, axiom,
% 2.42/2.61    (![A:$i,B:$i,C:$i,D:$i]:
% 2.42/2.61     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 2.42/2.61       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 2.42/2.61  thf('33', plain,
% 2.42/2.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.42/2.61         ((r2_hidden @ X2 @ X3)
% 2.42/2.61          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 2.42/2.61      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 2.42/2.61  thf('34', plain,
% 2.42/2.61      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C))
% 2.42/2.61         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 2.42/2.61      inference('sup-', [status(thm)], ['32', '33'])).
% 2.42/2.61  thf(d2_subset_1, axiom,
% 2.42/2.61    (![A:$i,B:$i]:
% 2.42/2.61     ( ( ( v1_xboole_0 @ A ) =>
% 2.42/2.61         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 2.42/2.61       ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.42/2.61         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 2.42/2.61  thf('35', plain,
% 2.42/2.61      (![X5 : $i, X6 : $i]:
% 2.42/2.61         (~ (r2_hidden @ X5 @ X6)
% 2.42/2.61          | (m1_subset_1 @ X5 @ X6)
% 2.42/2.61          | (v1_xboole_0 @ X6))),
% 2.42/2.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.42/2.61  thf('36', plain,
% 2.42/2.61      ((((v1_xboole_0 @ sk_C)
% 2.42/2.61         | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C)))
% 2.42/2.61         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 2.42/2.61      inference('sup-', [status(thm)], ['34', '35'])).
% 2.42/2.61  thf('37', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.42/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.61  thf('38', plain,
% 2.42/2.61      (((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C))
% 2.42/2.61         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 2.42/2.61      inference('clc', [status(thm)], ['36', '37'])).
% 2.42/2.61  thf('39', plain,
% 2.42/2.61      (~ ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 2.42/2.61      inference('demod', [status(thm)], ['27', '38'])).
% 2.42/2.61  thf('40', plain,
% 2.42/2.61      (((r2_hidden @ sk_F @ sk_B)) | 
% 2.42/2.61       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 2.42/2.61      inference('split', [status(esa)], ['5'])).
% 2.42/2.61  thf('41', plain,
% 2.42/2.61      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 2.42/2.61      inference('split', [status(esa)], ['5'])).
% 2.42/2.61  thf('42', plain,
% 2.42/2.61      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2))
% 2.42/2.61         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 2.42/2.61      inference('split', [status(esa)], ['0'])).
% 2.42/2.61  thf(d14_relat_1, axiom,
% 2.42/2.61    (![A:$i]:
% 2.42/2.61     ( ( v1_relat_1 @ A ) =>
% 2.42/2.61       ( ![B:$i,C:$i]:
% 2.42/2.61         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 2.42/2.61           ( ![D:$i]:
% 2.42/2.61             ( ( r2_hidden @ D @ C ) <=>
% 2.42/2.61               ( ?[E:$i]:
% 2.42/2.61                 ( ( r2_hidden @ E @ B ) & 
% 2.42/2.61                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 2.42/2.61  thf('43', plain,
% 2.42/2.61      (![X14 : $i, X15 : $i, X17 : $i, X19 : $i, X20 : $i]:
% 2.42/2.61         (((X17) != (k10_relat_1 @ X15 @ X14))
% 2.42/2.61          | (r2_hidden @ X19 @ X17)
% 2.42/2.61          | ~ (r2_hidden @ (k4_tarski @ X19 @ X20) @ X15)
% 2.42/2.61          | ~ (r2_hidden @ X20 @ X14)
% 2.42/2.61          | ~ (v1_relat_1 @ X15))),
% 2.42/2.61      inference('cnf', [status(esa)], [d14_relat_1])).
% 2.42/2.61  thf('44', plain,
% 2.42/2.61      (![X14 : $i, X15 : $i, X19 : $i, X20 : $i]:
% 2.42/2.61         (~ (v1_relat_1 @ X15)
% 2.42/2.61          | ~ (r2_hidden @ X20 @ X14)
% 2.42/2.61          | ~ (r2_hidden @ (k4_tarski @ X19 @ X20) @ X15)
% 2.42/2.61          | (r2_hidden @ X19 @ (k10_relat_1 @ X15 @ X14)))),
% 2.42/2.61      inference('simplify', [status(thm)], ['43'])).
% 2.42/2.61  thf('45', plain,
% 2.42/2.61      ((![X0 : $i]:
% 2.42/2.61          ((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ X0))
% 2.42/2.61           | ~ (r2_hidden @ sk_F @ X0)
% 2.42/2.61           | ~ (v1_relat_1 @ sk_D_2)))
% 2.42/2.61         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 2.42/2.61      inference('sup-', [status(thm)], ['42', '44'])).
% 2.42/2.61  thf('46', plain, ((v1_relat_1 @ sk_D_2)),
% 2.42/2.61      inference('demod', [status(thm)], ['12', '13'])).
% 2.42/2.61  thf('47', plain,
% 2.42/2.61      ((![X0 : $i]:
% 2.42/2.61          ((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ X0))
% 2.42/2.61           | ~ (r2_hidden @ sk_F @ X0)))
% 2.42/2.61         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 2.42/2.61      inference('demod', [status(thm)], ['45', '46'])).
% 2.42/2.61  thf('48', plain,
% 2.42/2.61      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 2.42/2.61         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 2.42/2.61             ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 2.42/2.61      inference('sup-', [status(thm)], ['41', '47'])).
% 2.42/2.61  thf('49', plain,
% 2.42/2.61      (![X0 : $i]:
% 2.42/2.61         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0)
% 2.42/2.61           = (k10_relat_1 @ sk_D_2 @ X0))),
% 2.42/2.61      inference('sup-', [status(thm)], ['2', '3'])).
% 2.42/2.61  thf('50', plain,
% 2.42/2.61      (![X31 : $i]:
% 2.42/2.61         (~ (m1_subset_1 @ X31 @ sk_C)
% 2.42/2.61          | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X31) @ sk_D_2)
% 2.42/2.61          | ~ (r2_hidden @ X31 @ sk_B)
% 2.42/2.61          | ~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 2.42/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.61  thf('51', plain,
% 2.42/2.61      ((~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))
% 2.42/2.61         <= (~
% 2.42/2.61             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 2.42/2.61      inference('split', [status(esa)], ['50'])).
% 2.42/2.61  thf('52', plain,
% 2.42/2.61      ((~ (r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 2.42/2.61         <= (~
% 2.42/2.61             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 2.42/2.61      inference('sup-', [status(thm)], ['49', '51'])).
% 2.42/2.61  thf('53', plain,
% 2.42/2.61      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 2.42/2.61       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))) | 
% 2.42/2.61       ~ ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2))),
% 2.42/2.61      inference('sup-', [status(thm)], ['48', '52'])).
% 2.42/2.61  thf('54', plain, ($false),
% 2.42/2.61      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '53'])).
% 2.42/2.61  
% 2.42/2.61  % SZS output end Refutation
% 2.42/2.61  
% 2.42/2.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
