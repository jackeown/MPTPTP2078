%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Kdx2wswG6c

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 192 expanded)
%              Number of leaves         :   28 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  980 (3167 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('6',plain,(
    v5_relat_1 @ sk_D_1 @ sk_C ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k8_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k10_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0 )
      = ( k10_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','11'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k10_relat_1 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X3 @ X4 ) @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ ( k2_relat_1 @ sk_D_1 ) ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('17',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ ( k2_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( v5_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_1 )
        | ~ ( v5_relat_1 @ sk_D_1 @ X0 )
        | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ X0 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ~ ( v5_relat_1 @ sk_D_1 @ X0 )
        | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ X0 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','22'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('25',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','11'])).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k10_relat_1 @ X5 @ X3 ) )
      | ( r2_hidden @ ( k4_tarski @ X4 @ ( sk_D @ X5 @ X3 @ X4 ) ) @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('28',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) ) @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('30',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X22: $i] :
      ( ~ ( m1_subset_1 @ X22 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X22 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X22 @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X22 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) )
   <= ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X22 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C ) )
   <= ( ! [X22: $i] :
          ( ~ ( m1_subset_1 @ X22 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X22 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X22 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','11'])).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k10_relat_1 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X3 @ X4 ) @ X3 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('36',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('38',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C )
   <= ( ! [X22: $i] :
          ( ~ ( m1_subset_1 @ X22 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X22 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X22 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
    | ~ ! [X22: $i] :
          ( ~ ( m1_subset_1 @ X22 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X22 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','39'])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
   <= ( m1_subset_1 @ sk_F @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('42',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('43',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X22 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) )
   <= ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X22 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('45',plain,
    ( ( ~ ( r2_hidden @ sk_F @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ sk_C ) )
   <= ( ! [X22: $i] :
          ( ~ ( m1_subset_1 @ X22 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X22 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X22 @ sk_B ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( m1_subset_1 @ sk_F @ sk_C )
   <= ( ! [X22: $i] :
          ( ~ ( m1_subset_1 @ X22 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X22 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X22 @ sk_B ) )
      & ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
    | ~ ! [X22: $i] :
          ( ~ ( m1_subset_1 @ X22 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X22 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X22 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F @ sk_C )
    | ~ ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
    | ! [X22: $i] :
        ( ~ ( m1_subset_1 @ X22 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X22 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('49',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('50',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('51',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X2 ) @ X5 )
      | ~ ( r2_hidden @ X2 @ ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ X4 @ ( k10_relat_1 @ X5 @ X3 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_1 )
        | ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('57',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 )
      | ( r2_hidden @ X10 @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('58',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('60',plain,
    ( ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('62',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['50','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0 )
      = ( k10_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('64',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('65',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','40','47','48','49','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Kdx2wswG6c
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 127 iterations in 0.042s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(t53_relset_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( m1_subset_1 @
% 0.20/0.50                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.20/0.50                   ( ![E:$i]:
% 0.20/0.50                     ( ( m1_subset_1 @ E @ A ) =>
% 0.20/0.50                       ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.20/0.50                         ( ?[F:$i]:
% 0.20/0.50                           ( ( r2_hidden @ F @ B ) & 
% 0.20/0.50                             ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.20/0.50                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.50                  ( ![D:$i]:
% 0.20/0.50                    ( ( m1_subset_1 @
% 0.20/0.50                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.20/0.50                      ( ![E:$i]:
% 0.20/0.50                        ( ( m1_subset_1 @ E @ A ) =>
% 0.20/0.50                          ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.20/0.50                            ( ?[F:$i]:
% 0.20/0.50                              ( ( r2_hidden @ F @ B ) & 
% 0.20/0.50                                ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.20/0.50                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t53_relset_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)
% 0.20/0.50        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)) | 
% 0.20/0.50       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (((m1_subset_1 @ sk_F @ sk_C)
% 0.20/0.50        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (((m1_subset_1 @ sk_F @ sk_C)) | 
% 0.20/0.50       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc2_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.50         ((v5_relat_1 @ X15 @ X17)
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.50  thf('6', plain, ((v5_relat_1 @ sk_D_1 @ sk_C)),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.20/0.50          | ((k8_relset_1 @ X19 @ X20 @ X18 @ X21) = (k10_relat_1 @ X18 @ X21)))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0)
% 0.20/0.50           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (((r2_hidden @ sk_F @ sk_B)
% 0.20/0.50        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))
% 0.20/0.50         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.50      inference('split', [status(esa)], ['10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.20/0.50         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['9', '11'])).
% 0.20/0.50  thf(t166_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ C ) =>
% 0.20/0.50       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.20/0.50         ( ?[D:$i]:
% 0.20/0.50           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.50             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.20/0.50             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X4 @ (k10_relat_1 @ X5 @ X3))
% 0.20/0.50          | (r2_hidden @ (sk_D @ X5 @ X3 @ X4) @ (k2_relat_1 @ X5))
% 0.20/0.50          | ~ (v1_relat_1 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (((~ (v1_relat_1 @ sk_D_1)
% 0.20/0.50         | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ (k2_relat_1 @ sk_D_1))))
% 0.20/0.50         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc1_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( v1_relat_1 @ C ) ))).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.50         ((v1_relat_1 @ X12)
% 0.20/0.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.50  thf('17', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ (k2_relat_1 @ sk_D_1)))
% 0.20/0.50         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.50      inference('demod', [status(thm)], ['14', '17'])).
% 0.20/0.50  thf(t202_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X6 @ (k2_relat_1 @ X7))
% 0.20/0.50          | (r2_hidden @ X6 @ X8)
% 0.20/0.50          | ~ (v5_relat_1 @ X7 @ X8)
% 0.20/0.50          | ~ (v1_relat_1 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (~ (v1_relat_1 @ sk_D_1)
% 0.20/0.50           | ~ (v5_relat_1 @ sk_D_1 @ X0)
% 0.20/0.50           | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ X0)))
% 0.20/0.50         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (~ (v5_relat_1 @ sk_D_1 @ X0)
% 0.20/0.50           | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ X0)))
% 0.20/0.50         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C))
% 0.20/0.50         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '22'])).
% 0.20/0.50  thf(t1_subset, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C))
% 0.20/0.50         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.20/0.50         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['9', '11'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X4 @ (k10_relat_1 @ X5 @ X3))
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ X4 @ (sk_D @ X5 @ X3 @ X4)) @ X5)
% 0.20/0.50          | ~ (v1_relat_1 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (((~ (v1_relat_1 @ sk_D_1)
% 0.20/0.50         | (r2_hidden @ (k4_tarski @ sk_E @ (sk_D @ sk_D_1 @ sk_B @ sk_E)) @ 
% 0.20/0.50            sk_D_1)))
% 0.20/0.50         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('29', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (((r2_hidden @ (k4_tarski @ sk_E @ (sk_D @ sk_D_1 @ sk_B @ sk_E)) @ 
% 0.20/0.50         sk_D_1))
% 0.20/0.50         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.50      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X22 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X22 @ sk_C)
% 0.20/0.50          | ~ (r2_hidden @ (k4_tarski @ sk_E @ X22) @ sk_D_1)
% 0.20/0.50          | ~ (r2_hidden @ X22 @ sk_B)
% 0.20/0.50          | ~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      ((![X22 : $i]:
% 0.20/0.50          (~ (m1_subset_1 @ X22 @ sk_C)
% 0.20/0.50           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X22) @ sk_D_1)
% 0.20/0.50           | ~ (r2_hidden @ X22 @ sk_B)))
% 0.20/0.50         <= ((![X22 : $i]:
% 0.20/0.50                (~ (m1_subset_1 @ X22 @ sk_C)
% 0.20/0.50                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X22) @ sk_D_1)
% 0.20/0.50                 | ~ (r2_hidden @ X22 @ sk_B))))),
% 0.20/0.50      inference('split', [status(esa)], ['31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (((~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B)
% 0.20/0.50         | ~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C)))
% 0.20/0.50         <= ((![X22 : $i]:
% 0.20/0.50                (~ (m1_subset_1 @ X22 @ sk_C)
% 0.20/0.50                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X22) @ sk_D_1)
% 0.20/0.50                 | ~ (r2_hidden @ X22 @ sk_B))) & 
% 0.20/0.50             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['30', '32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.20/0.50         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['9', '11'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X4 @ (k10_relat_1 @ X5 @ X3))
% 0.20/0.50          | (r2_hidden @ (sk_D @ X5 @ X3 @ X4) @ X3)
% 0.20/0.50          | ~ (v1_relat_1 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (((~ (v1_relat_1 @ sk_D_1)
% 0.20/0.50         | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B)))
% 0.20/0.50         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf('37', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B))
% 0.20/0.50         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.50      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C))
% 0.20/0.50         <= ((![X22 : $i]:
% 0.20/0.50                (~ (m1_subset_1 @ X22 @ sk_C)
% 0.20/0.50                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X22) @ sk_D_1)
% 0.20/0.50                 | ~ (r2_hidden @ X22 @ sk_B))) & 
% 0.20/0.50             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.50      inference('demod', [status(thm)], ['33', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))) | 
% 0.20/0.50       ~
% 0.20/0.50       (![X22 : $i]:
% 0.20/0.50          (~ (m1_subset_1 @ X22 @ sk_C)
% 0.20/0.50           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X22) @ sk_D_1)
% 0.20/0.50           | ~ (r2_hidden @ X22 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['25', '39'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (((m1_subset_1 @ sk_F @ sk_C)) <= (((m1_subset_1 @ sk_F @ sk_C)))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['10'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1))
% 0.20/0.50         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      ((![X22 : $i]:
% 0.20/0.50          (~ (m1_subset_1 @ X22 @ sk_C)
% 0.20/0.50           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X22) @ sk_D_1)
% 0.20/0.50           | ~ (r2_hidden @ X22 @ sk_B)))
% 0.20/0.50         <= ((![X22 : $i]:
% 0.20/0.50                (~ (m1_subset_1 @ X22 @ sk_C)
% 0.20/0.50                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X22) @ sk_D_1)
% 0.20/0.50                 | ~ (r2_hidden @ X22 @ sk_B))))),
% 0.20/0.50      inference('split', [status(esa)], ['31'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (((~ (r2_hidden @ sk_F @ sk_B) | ~ (m1_subset_1 @ sk_F @ sk_C)))
% 0.20/0.50         <= ((![X22 : $i]:
% 0.20/0.50                (~ (m1_subset_1 @ X22 @ sk_C)
% 0.20/0.50                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X22) @ sk_D_1)
% 0.20/0.50                 | ~ (r2_hidden @ X22 @ sk_B))) & 
% 0.20/0.50             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      ((~ (m1_subset_1 @ sk_F @ sk_C))
% 0.20/0.50         <= ((![X22 : $i]:
% 0.20/0.50                (~ (m1_subset_1 @ X22 @ sk_C)
% 0.20/0.50                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X22) @ sk_D_1)
% 0.20/0.50                 | ~ (r2_hidden @ X22 @ sk_B))) & 
% 0.20/0.50             ((r2_hidden @ sk_F @ sk_B)) & 
% 0.20/0.50             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['42', '45'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)) | 
% 0.20/0.50       ~
% 0.20/0.50       (![X22 : $i]:
% 0.20/0.50          (~ (m1_subset_1 @ X22 @ sk_C)
% 0.20/0.50           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X22) @ sk_D_1)
% 0.20/0.50           | ~ (r2_hidden @ X22 @ sk_B))) | 
% 0.20/0.50       ~ ((m1_subset_1 @ sk_F @ sk_C)) | ~ ((r2_hidden @ sk_F @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['41', '46'])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))) | 
% 0.20/0.50       (![X22 : $i]:
% 0.20/0.50          (~ (m1_subset_1 @ X22 @ sk_C)
% 0.20/0.50           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X22) @ sk_D_1)
% 0.20/0.50           | ~ (r2_hidden @ X22 @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['31'])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.20/0.50       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['10'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['10'])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1))
% 0.20/0.50         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.50          | ~ (r2_hidden @ (k4_tarski @ X4 @ X2) @ X5)
% 0.20/0.50          | ~ (r2_hidden @ X2 @ (k2_relat_1 @ X5))
% 0.20/0.50          | (r2_hidden @ X4 @ (k10_relat_1 @ X5 @ X3))
% 0.20/0.50          | ~ (v1_relat_1 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (~ (v1_relat_1 @ sk_D_1)
% 0.20/0.50           | (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.20/0.50           | ~ (r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1))
% 0.20/0.50           | ~ (r2_hidden @ sk_F @ X0)))
% 0.20/0.50         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.50  thf('54', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          ((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.20/0.50           | ~ (r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1))
% 0.20/0.50           | ~ (r2_hidden @ sk_F @ X0)))
% 0.20/0.50         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1))
% 0.20/0.50         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf(t20_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ C ) =>
% 0.20/0.50       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.20/0.50         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.50           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.50         (~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11)
% 0.20/0.50          | (r2_hidden @ X10 @ (k2_relat_1 @ X11))
% 0.20/0.50          | ~ (v1_relat_1 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (((~ (v1_relat_1 @ sk_D_1) | (r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1))))
% 0.20/0.50         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.50  thf('59', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      (((r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1)))
% 0.20/0.50         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          ((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.20/0.50           | ~ (r2_hidden @ sk_F @ X0)))
% 0.20/0.50         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['55', '60'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.20/0.50         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.20/0.50             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['50', '61'])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0)
% 0.20/0.50           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      ((~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.50      inference('split', [status(esa)], ['31'])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      ((~ (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 0.20/0.50       ~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)) | 
% 0.20/0.50       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['62', '65'])).
% 0.20/0.50  thf('67', plain, ($false),
% 0.20/0.50      inference('sat_resolution*', [status(thm)],
% 0.20/0.50                ['1', '3', '40', '47', '48', '49', '66'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
