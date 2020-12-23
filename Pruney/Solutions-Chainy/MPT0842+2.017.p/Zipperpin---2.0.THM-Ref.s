%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aGWeDJdXKg

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 210 expanded)
%              Number of leaves         :   29 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  994 (3251 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k8_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k10_relat_1 @ X19 @ X22 ) ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k10_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X7 @ X8 ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ ( k2_relat_1 @ sk_D_1 ) ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('19',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ ( k2_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X11 ) )
      | ( r2_hidden @ X10 @ X12 )
      | ~ ( v5_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_1 )
        | ~ ( v5_relat_1 @ sk_D_1 @ X0 )
        | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ X0 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ~ ( v5_relat_1 @ sk_D_1 @ X0 )
        | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ X0 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','24'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('27',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','11'])).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k10_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_D @ X9 @ X7 @ X8 ) ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('30',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) ) @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('32',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X23: $i] :
      ( ~ ( m1_subset_1 @ X23 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X23 @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X23 @ sk_B ) )
   <= ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X23 @ sk_B ) ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C ) )
   <= ( ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X23 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','11'])).

thf('37',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k10_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X7 @ X8 ) @ X7 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('38',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('40',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C )
   <= ( ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X23 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
    | ~ ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X23 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
   <= ( m1_subset_1 @ sk_F @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('44',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('45',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X23 @ sk_B ) )
   <= ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X23 @ sk_B ) ) ),
    inference(split,[status(esa)],['33'])).

thf('47',plain,
    ( ( ~ ( r2_hidden @ sk_F @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ sk_C ) )
   <= ( ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X23 @ sk_B ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( m1_subset_1 @ sk_F @ sk_C )
   <= ( ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X23 @ sk_B ) )
      & ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
    | ~ ! [X23: $i] :
          ( ~ ( m1_subset_1 @ X23 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X23 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F @ sk_C )
    | ~ ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
    | ! [X23: $i] :
        ( ~ ( m1_subset_1 @ X23 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X23 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X23 @ sk_B ) ) ),
    inference(split,[status(esa)],['33'])).

thf('51',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('52',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('53',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X6 ) @ X9 )
      | ~ ( r2_hidden @ X6 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ X8 @ ( k10_relat_1 @ X9 @ X7 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_1 )
        | ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('59',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 )
      | ( r2_hidden @ X14 @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('60',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('62',plain,
    ( ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['57','62'])).

thf('64',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['52','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0 )
      = ( k10_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('66',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['33'])).

thf('67',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','42','49','50','51','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aGWeDJdXKg
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 127 iterations in 0.037s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(t53_relset_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( m1_subset_1 @
% 0.20/0.49                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.20/0.49                   ( ![E:$i]:
% 0.20/0.49                     ( ( m1_subset_1 @ E @ A ) =>
% 0.20/0.49                       ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.20/0.49                         ( ?[F:$i]:
% 0.20/0.49                           ( ( r2_hidden @ F @ B ) & 
% 0.20/0.49                             ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.20/0.49                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.49              ( ![C:$i]:
% 0.20/0.49                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.49                  ( ![D:$i]:
% 0.20/0.49                    ( ( m1_subset_1 @
% 0.20/0.49                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.20/0.49                      ( ![E:$i]:
% 0.20/0.49                        ( ( m1_subset_1 @ E @ A ) =>
% 0.20/0.49                          ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.20/0.49                            ( ?[F:$i]:
% 0.20/0.49                              ( ( r2_hidden @ F @ B ) & 
% 0.20/0.49                                ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.20/0.49                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t53_relset_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)
% 0.20/0.49        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)) | 
% 0.20/0.49       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (((m1_subset_1 @ sk_F @ sk_C)
% 0.20/0.49        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (((m1_subset_1 @ sk_F @ sk_C)) | 
% 0.20/0.49       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc2_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.49         ((v5_relat_1 @ X16 @ X18)
% 0.20/0.49          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.49  thf('6', plain, ((v5_relat_1 @ sk_D_1 @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.20/0.49          | ((k8_relset_1 @ X20 @ X21 @ X19 @ X22) = (k10_relat_1 @ X19 @ X22)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0)
% 0.20/0.49           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (((r2_hidden @ sk_F @ sk_B)
% 0.20/0.49        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))
% 0.20/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.20/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['9', '11'])).
% 0.20/0.49  thf(t166_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ C ) =>
% 0.20/0.49       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.20/0.49         ( ?[D:$i]:
% 0.20/0.49           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.49             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.20/0.49             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X8 @ (k10_relat_1 @ X9 @ X7))
% 0.20/0.49          | (r2_hidden @ (sk_D @ X9 @ X7 @ X8) @ (k2_relat_1 @ X9))
% 0.20/0.49          | ~ (v1_relat_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (((~ (v1_relat_1 @ sk_D_1)
% 0.20/0.49         | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ (k2_relat_1 @ sk_D_1))))
% 0.20/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc2_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.20/0.49          | (v1_relat_1 @ X2)
% 0.20/0.49          | ~ (v1_relat_1 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_D_1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf(fc6_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.49  thf('19', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ (k2_relat_1 @ sk_D_1)))
% 0.20/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '19'])).
% 0.20/0.49  thf(t202_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X10 @ (k2_relat_1 @ X11))
% 0.20/0.49          | (r2_hidden @ X10 @ X12)
% 0.20/0.49          | ~ (v5_relat_1 @ X11 @ X12)
% 0.20/0.49          | ~ (v1_relat_1 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (~ (v1_relat_1 @ sk_D_1)
% 0.20/0.49           | ~ (v5_relat_1 @ sk_D_1 @ X0)
% 0.20/0.49           | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ X0)))
% 0.20/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf('23', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (~ (v5_relat_1 @ sk_D_1 @ X0)
% 0.20/0.49           | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ X0)))
% 0.20/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C))
% 0.20/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '24'])).
% 0.20/0.49  thf(t1_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C))
% 0.20/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.20/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['9', '11'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X8 @ (k10_relat_1 @ X9 @ X7))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X8 @ (sk_D @ X9 @ X7 @ X8)) @ X9)
% 0.20/0.49          | ~ (v1_relat_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (((~ (v1_relat_1 @ sk_D_1)
% 0.20/0.49         | (r2_hidden @ (k4_tarski @ sk_E @ (sk_D @ sk_D_1 @ sk_B @ sk_E)) @ 
% 0.20/0.49            sk_D_1)))
% 0.20/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf('31', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_E @ (sk_D @ sk_D_1 @ sk_B @ sk_E)) @ 
% 0.20/0.49         sk_D_1))
% 0.20/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.49      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X23 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X23 @ sk_C)
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.20/0.49          | ~ (r2_hidden @ X23 @ sk_B)
% 0.20/0.49          | ~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      ((![X23 : $i]:
% 0.20/0.49          (~ (m1_subset_1 @ X23 @ sk_C)
% 0.20/0.49           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.20/0.49           | ~ (r2_hidden @ X23 @ sk_B)))
% 0.20/0.49         <= ((![X23 : $i]:
% 0.20/0.49                (~ (m1_subset_1 @ X23 @ sk_C)
% 0.20/0.49                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.20/0.49                 | ~ (r2_hidden @ X23 @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (((~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B)
% 0.20/0.49         | ~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C)))
% 0.20/0.49         <= ((![X23 : $i]:
% 0.20/0.49                (~ (m1_subset_1 @ X23 @ sk_C)
% 0.20/0.49                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.20/0.49                 | ~ (r2_hidden @ X23 @ sk_B))) & 
% 0.20/0.49             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.20/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['9', '11'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X8 @ (k10_relat_1 @ X9 @ X7))
% 0.20/0.49          | (r2_hidden @ (sk_D @ X9 @ X7 @ X8) @ X7)
% 0.20/0.49          | ~ (v1_relat_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (((~ (v1_relat_1 @ sk_D_1)
% 0.20/0.49         | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B)))
% 0.20/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.49  thf('39', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B))
% 0.20/0.49         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.49      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C))
% 0.20/0.49         <= ((![X23 : $i]:
% 0.20/0.49                (~ (m1_subset_1 @ X23 @ sk_C)
% 0.20/0.49                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.20/0.49                 | ~ (r2_hidden @ X23 @ sk_B))) & 
% 0.20/0.49             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.49      inference('demod', [status(thm)], ['35', '40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))) | 
% 0.20/0.49       ~
% 0.20/0.49       (![X23 : $i]:
% 0.20/0.49          (~ (m1_subset_1 @ X23 @ sk_C)
% 0.20/0.49           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.20/0.49           | ~ (r2_hidden @ X23 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (((m1_subset_1 @ sk_F @ sk_C)) <= (((m1_subset_1 @ sk_F @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['10'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      ((![X23 : $i]:
% 0.20/0.49          (~ (m1_subset_1 @ X23 @ sk_C)
% 0.20/0.49           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.20/0.49           | ~ (r2_hidden @ X23 @ sk_B)))
% 0.20/0.49         <= ((![X23 : $i]:
% 0.20/0.49                (~ (m1_subset_1 @ X23 @ sk_C)
% 0.20/0.49                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.20/0.49                 | ~ (r2_hidden @ X23 @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['33'])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (((~ (r2_hidden @ sk_F @ sk_B) | ~ (m1_subset_1 @ sk_F @ sk_C)))
% 0.20/0.49         <= ((![X23 : $i]:
% 0.20/0.49                (~ (m1_subset_1 @ X23 @ sk_C)
% 0.20/0.49                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.20/0.49                 | ~ (r2_hidden @ X23 @ sk_B))) & 
% 0.20/0.49             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      ((~ (m1_subset_1 @ sk_F @ sk_C))
% 0.20/0.49         <= ((![X23 : $i]:
% 0.20/0.49                (~ (m1_subset_1 @ X23 @ sk_C)
% 0.20/0.49                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.20/0.49                 | ~ (r2_hidden @ X23 @ sk_B))) & 
% 0.20/0.49             ((r2_hidden @ sk_F @ sk_B)) & 
% 0.20/0.49             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['44', '47'])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)) | 
% 0.20/0.49       ~
% 0.20/0.49       (![X23 : $i]:
% 0.20/0.49          (~ (m1_subset_1 @ X23 @ sk_C)
% 0.20/0.49           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.20/0.49           | ~ (r2_hidden @ X23 @ sk_B))) | 
% 0.20/0.49       ~ ((m1_subset_1 @ sk_F @ sk_C)) | ~ ((r2_hidden @ sk_F @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['43', '48'])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))) | 
% 0.20/0.49       (![X23 : $i]:
% 0.20/0.49          (~ (m1_subset_1 @ X23 @ sk_C)
% 0.20/0.49           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X23) @ sk_D_1)
% 0.20/0.49           | ~ (r2_hidden @ X23 @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['33'])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.20/0.49       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['10'])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['10'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X6 @ X7)
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X8 @ X6) @ X9)
% 0.20/0.49          | ~ (r2_hidden @ X6 @ (k2_relat_1 @ X9))
% 0.20/0.49          | (r2_hidden @ X8 @ (k10_relat_1 @ X9 @ X7))
% 0.20/0.49          | ~ (v1_relat_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (~ (v1_relat_1 @ sk_D_1)
% 0.20/0.49           | (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.20/0.49           | ~ (r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1))
% 0.20/0.49           | ~ (r2_hidden @ sk_F @ X0)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.49  thf('56', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          ((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.20/0.49           | ~ (r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1))
% 0.20/0.49           | ~ (r2_hidden @ sk_F @ X0)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf(t20_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ C ) =>
% 0.20/0.49       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.20/0.49         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.49           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15)
% 0.20/0.49          | (r2_hidden @ X14 @ (k2_relat_1 @ X15))
% 0.20/0.49          | ~ (v1_relat_1 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      (((~ (v1_relat_1 @ sk_D_1) | (r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1))))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.49  thf('61', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      (((r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          ((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.20/0.49           | ~ (r2_hidden @ sk_F @ X0)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['57', '62'])).
% 0.20/0.49  thf('64', plain,
% 0.20/0.49      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.20/0.49         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.20/0.49             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['52', '63'])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0)
% 0.20/0.49           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('66', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['33'])).
% 0.20/0.49  thf('67', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.20/0.49         <= (~
% 0.20/0.49             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.49  thf('68', plain,
% 0.20/0.49      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 0.20/0.49       ~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)) | 
% 0.20/0.49       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['64', '67'])).
% 0.20/0.49  thf('69', plain, ($false),
% 0.20/0.49      inference('sat_resolution*', [status(thm)],
% 0.20/0.49                ['1', '3', '42', '49', '50', '51', '68'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
