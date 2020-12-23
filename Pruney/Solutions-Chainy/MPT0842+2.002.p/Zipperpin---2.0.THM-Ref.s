%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ifn3Q6P8xd

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 154 expanded)
%              Number of leaves         :   27 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  803 (2425 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ X27 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X27 ) @ sk_D_2 )
      | ~ ( r2_hidden @ X27 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X27 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X27 @ sk_B ) )
    | ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('6',plain,(
    v5_relat_1 @ sk_D_2 @ sk_C ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k8_relset_1 @ X24 @ X25 @ X23 @ X26 )
        = ( k10_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0 )
      = ( k10_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k10_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X11 @ X12 ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ ( k2_relat_1 @ sk_D_2 ) ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('17',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ ( k2_relat_1 @ sk_D_2 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k2_relat_1 @ X15 ) )
      | ( r2_hidden @ X14 @ X16 )
      | ~ ( v5_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_2 )
        | ~ ( v5_relat_1 @ sk_D_2 @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ X0 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ~ ( v5_relat_1 @ sk_D_2 @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ X0 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
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
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','11'])).

thf('27',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k10_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( sk_D_1 @ X13 @ X11 @ X12 ) ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('28',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) ) @ sk_D_2 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('30',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) ) @ sk_D_2 )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X27 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X27 @ sk_B ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X27 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X27 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('32',plain,
    ( ( ~ ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C ) )
   <= ( ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X27 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X27 @ sk_B ) )
      & ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','11'])).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k10_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X11 @ X12 ) @ X11 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('35',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('37',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C )
   <= ( ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X27 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X27 @ sk_B ) )
      & ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,
    ( ~ ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X27 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X27 @ sk_B ) )
    | ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('41',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

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
    ! [X3: $i,X4: $i,X6: $i,X8: $i,X9: $i] :
      ( ( X6
       != ( k10_relat_1 @ X4 @ X3 ) )
      | ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X4 )
      | ~ ( r2_hidden @ X9 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('44',plain,(
    ! [X3: $i,X4: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( r2_hidden @ X9 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X4 )
      | ( r2_hidden @ X8 @ ( k10_relat_1 @ X4 @ X3 ) ) ) ),
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
    inference('sup-',[status(thm)],['15','16'])).

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
    inference('sup-',[status(thm)],['7','8'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','39','40','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ifn3Q6P8xd
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 80 iterations in 0.064s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.20/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.52  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.52  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(t53_relset_1, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.52               ( ![D:$i]:
% 0.20/0.52                 ( ( m1_subset_1 @
% 0.20/0.52                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.20/0.52                   ( ![E:$i]:
% 0.20/0.52                     ( ( m1_subset_1 @ E @ A ) =>
% 0.20/0.52                       ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.20/0.52                         ( ?[F:$i]:
% 0.20/0.52                           ( ( r2_hidden @ F @ B ) & 
% 0.20/0.52                             ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.20/0.52                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.52              ( ![C:$i]:
% 0.20/0.52                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.52                  ( ![D:$i]:
% 0.20/0.52                    ( ( m1_subset_1 @
% 0.20/0.52                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.20/0.52                      ( ![E:$i]:
% 0.20/0.52                        ( ( m1_subset_1 @ E @ A ) =>
% 0.20/0.52                          ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.20/0.52                            ( ?[F:$i]:
% 0.20/0.52                              ( ( r2_hidden @ F @ B ) & 
% 0.20/0.52                                ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.20/0.52                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t53_relset_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)
% 0.20/0.52        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)) | 
% 0.20/0.52       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X27 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X27 @ sk_C)
% 0.20/0.52          | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X27) @ sk_D_2)
% 0.20/0.52          | ~ (r2_hidden @ X27 @ sk_B)
% 0.20/0.52          | ~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      ((![X27 : $i]:
% 0.20/0.52          (~ (m1_subset_1 @ X27 @ sk_C)
% 0.20/0.52           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X27) @ sk_D_2)
% 0.20/0.52           | ~ (r2_hidden @ X27 @ sk_B))) | 
% 0.20/0.52       ~ ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(cc2_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.52         ((v5_relat_1 @ X20 @ X22)
% 0.20/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.52  thf('6', plain, ((v5_relat_1 @ sk_D_2 @ sk_C)),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.20/0.52          | ((k8_relset_1 @ X24 @ X25 @ X23 @ X26) = (k10_relat_1 @ X23 @ X26)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0)
% 0.20/0.52           = (k10_relat_1 @ sk_D_2 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (((r2_hidden @ sk_F @ sk_B)
% 0.20/0.52        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))
% 0.20/0.52         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['10'])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.20/0.52         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['9', '11'])).
% 0.20/0.52  thf(t166_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ C ) =>
% 0.20/0.52       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.20/0.52         ( ?[D:$i]:
% 0.20/0.52           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.52             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.20/0.52             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X12 @ (k10_relat_1 @ X13 @ X11))
% 0.20/0.52          | (r2_hidden @ (sk_D_1 @ X13 @ X11 @ X12) @ (k2_relat_1 @ X13))
% 0.20/0.52          | ~ (v1_relat_1 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (((~ (v1_relat_1 @ sk_D_2)
% 0.20/0.52         | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ 
% 0.20/0.52            (k2_relat_1 @ sk_D_2))))
% 0.20/0.52         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(cc1_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( v1_relat_1 @ C ) ))).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.52         ((v1_relat_1 @ X17)
% 0.20/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.52  thf('17', plain, ((v1_relat_1 @ sk_D_2)),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ (k2_relat_1 @ sk_D_2)))
% 0.20/0.52         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '17'])).
% 0.20/0.52  thf(t202_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X14 @ (k2_relat_1 @ X15))
% 0.20/0.52          | (r2_hidden @ X14 @ X16)
% 0.20/0.52          | ~ (v5_relat_1 @ X15 @ X16)
% 0.20/0.52          | ~ (v1_relat_1 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          (~ (v1_relat_1 @ sk_D_2)
% 0.20/0.52           | ~ (v5_relat_1 @ sk_D_2 @ X0)
% 0.20/0.52           | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ X0)))
% 0.20/0.52         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('21', plain, ((v1_relat_1 @ sk_D_2)),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          (~ (v5_relat_1 @ sk_D_2 @ X0)
% 0.20/0.52           | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ X0)))
% 0.20/0.52         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C))
% 0.20/0.52         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '22'])).
% 0.20/0.52  thf(t1_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C))
% 0.20/0.52         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.20/0.52         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['9', '11'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X12 @ (k10_relat_1 @ X13 @ X11))
% 0.20/0.52          | (r2_hidden @ (k4_tarski @ X12 @ (sk_D_1 @ X13 @ X11 @ X12)) @ X13)
% 0.20/0.52          | ~ (v1_relat_1 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (((~ (v1_relat_1 @ sk_D_2)
% 0.20/0.52         | (r2_hidden @ 
% 0.20/0.52            (k4_tarski @ sk_E_2 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2)) @ sk_D_2)))
% 0.20/0.52         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain, ((v1_relat_1 @ sk_D_2)),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (((r2_hidden @ 
% 0.20/0.52         (k4_tarski @ sk_E_2 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2)) @ sk_D_2))
% 0.20/0.52         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      ((![X27 : $i]:
% 0.20/0.52          (~ (m1_subset_1 @ X27 @ sk_C)
% 0.20/0.52           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X27) @ sk_D_2)
% 0.20/0.52           | ~ (r2_hidden @ X27 @ sk_B)))
% 0.20/0.52         <= ((![X27 : $i]:
% 0.20/0.52                (~ (m1_subset_1 @ X27 @ sk_C)
% 0.20/0.52                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X27) @ sk_D_2)
% 0.20/0.52                 | ~ (r2_hidden @ X27 @ sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (((~ (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B)
% 0.20/0.52         | ~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C)))
% 0.20/0.52         <= ((![X27 : $i]:
% 0.20/0.52                (~ (m1_subset_1 @ X27 @ sk_C)
% 0.20/0.52                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X27) @ sk_D_2)
% 0.20/0.52                 | ~ (r2_hidden @ X27 @ sk_B))) & 
% 0.20/0.52             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.20/0.52         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['9', '11'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X12 @ (k10_relat_1 @ X13 @ X11))
% 0.20/0.52          | (r2_hidden @ (sk_D_1 @ X13 @ X11 @ X12) @ X11)
% 0.20/0.52          | ~ (v1_relat_1 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (((~ (v1_relat_1 @ sk_D_2)
% 0.20/0.52         | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B)))
% 0.20/0.52         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf('36', plain, ((v1_relat_1 @ sk_D_2)),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B))
% 0.20/0.52         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      ((~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C))
% 0.20/0.52         <= ((![X27 : $i]:
% 0.20/0.52                (~ (m1_subset_1 @ X27 @ sk_C)
% 0.20/0.52                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X27) @ sk_D_2)
% 0.20/0.52                 | ~ (r2_hidden @ X27 @ sk_B))) & 
% 0.20/0.52             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['32', '37'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (~
% 0.20/0.52       (![X27 : $i]:
% 0.20/0.52          (~ (m1_subset_1 @ X27 @ sk_C)
% 0.20/0.52           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X27) @ sk_D_2)
% 0.20/0.52           | ~ (r2_hidden @ X27 @ sk_B))) | 
% 0.20/0.52       ~ ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '38'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.20/0.52       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['10'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['10'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2))
% 0.20/0.52         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf(d14_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ![B:$i,C:$i]:
% 0.20/0.52         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.20/0.52           ( ![D:$i]:
% 0.20/0.52             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.52               ( ?[E:$i]:
% 0.20/0.52                 ( ( r2_hidden @ E @ B ) & 
% 0.20/0.52                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i, X6 : $i, X8 : $i, X9 : $i]:
% 0.20/0.52         (((X6) != (k10_relat_1 @ X4 @ X3))
% 0.20/0.52          | (r2_hidden @ X8 @ X6)
% 0.20/0.52          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X4)
% 0.20/0.52          | ~ (r2_hidden @ X9 @ X3)
% 0.20/0.52          | ~ (v1_relat_1 @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i, X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X4)
% 0.20/0.52          | ~ (r2_hidden @ X9 @ X3)
% 0.20/0.52          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X4)
% 0.20/0.52          | (r2_hidden @ X8 @ (k10_relat_1 @ X4 @ X3)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          ((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ X0))
% 0.20/0.52           | ~ (r2_hidden @ sk_F @ X0)
% 0.20/0.52           | ~ (v1_relat_1 @ sk_D_2)))
% 0.20/0.52         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['42', '44'])).
% 0.20/0.52  thf('46', plain, ((v1_relat_1 @ sk_D_2)),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          ((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ X0))
% 0.20/0.52           | ~ (r2_hidden @ sk_F @ X0)))
% 0.20/0.52         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.20/0.52      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.20/0.52         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.20/0.52             ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '47'])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0)
% 0.20/0.52           = (k10_relat_1 @ sk_D_2 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      ((~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))
% 0.20/0.52         <= (~
% 0.20/0.52             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      ((~ (r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.20/0.52         <= (~
% 0.20/0.52             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 0.20/0.52       ~ ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)) | 
% 0.20/0.52       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['48', '51'])).
% 0.20/0.52  thf('53', plain, ($false),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['1', '3', '39', '40', '52'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
