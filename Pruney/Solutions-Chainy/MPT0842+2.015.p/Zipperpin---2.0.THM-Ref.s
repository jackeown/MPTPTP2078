%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BgVNJ7EnKX

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:27 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 192 expanded)
%              Number of leaves         :   28 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  947 (3005 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

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

thf('2',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k8_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k10_relat_1 @ X24 @ X27 ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k10_relat_1 @ X17 @ X15 ) )
      | ( r2_hidden @ ( sk_D_1 @ X17 @ X15 @ X16 ) @ ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ ( k2_relat_1 @ sk_D_2 ) ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
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
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('19',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ ( k2_relat_1 @ sk_D_2 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k2_relat_1 @ X19 ) )
      | ( r2_hidden @ X18 @ X20 )
      | ~ ( v5_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_2 )
        | ~ ( v5_relat_1 @ sk_D_2 @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ X0 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['17','18'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ~ ( v5_relat_1 @ sk_D_2 @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ X0 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
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
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','11'])).

thf('29',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k10_relat_1 @ X17 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ ( sk_D_1 @ X17 @ X15 @ X16 ) ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('30',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) ) @ sk_D_2 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['17','18'])).

thf('32',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) ) @ sk_D_2 )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X28: $i] :
      ( ~ ( m1_subset_1 @ X28 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X28 ) @ sk_D_2 )
      | ~ ( r2_hidden @ X28 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X28 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X28 @ sk_B ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X28 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( ~ ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C ) )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X28 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X28 @ sk_B ) )
      & ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','11'])).

thf('37',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k10_relat_1 @ X17 @ X15 ) )
      | ( r2_hidden @ ( sk_D_1 @ X17 @ X15 @ X16 ) @ X15 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('38',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['17','18'])).

thf('40',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X28 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X28 @ sk_B ) )
      & ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) )
    | ~ ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X28 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
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
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X28 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X28 @ sk_B ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X28 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference(split,[status(esa)],['33'])).

thf('47',plain,
    ( ( ~ ( r2_hidden @ sk_F @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ sk_C ) )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X28 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X28 @ sk_B ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( m1_subset_1 @ sk_F @ sk_C )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X28 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X28 @ sk_B ) )
      & ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 )
    | ~ ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X28 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X28 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F @ sk_C )
    | ~ ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) )
    | ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X28 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X28 @ sk_B ) ) ),
    inference(split,[status(esa)],['33'])).

thf('51',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('52',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('53',plain,
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

thf('54',plain,(
    ! [X5: $i,X6: $i,X8: $i,X10: $i,X11: $i] :
      ( ( X8
       != ( k10_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X6 )
      | ~ ( r2_hidden @ X11 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('55',plain,(
    ! [X5: $i,X6: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( r2_hidden @ X11 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X6 )
      | ( r2_hidden @ X10 @ ( k10_relat_1 @ X6 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 )
        | ~ ( v1_relat_1 @ sk_D_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['17','18'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0 )
      = ( k10_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('61',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['33'])).

thf('62',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','42','49','50','51','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BgVNJ7EnKX
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 199 iterations in 0.137s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(sk_F_type, type, sk_F: $i).
% 0.42/0.60  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.42/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.60  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.42/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.42/0.60  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.42/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.60  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.42/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.42/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.42/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.60  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.42/0.60  thf(t53_relset_1, conjecture,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.42/0.60       ( ![B:$i]:
% 0.42/0.60         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.42/0.60           ( ![C:$i]:
% 0.42/0.60             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.42/0.60               ( ![D:$i]:
% 0.42/0.60                 ( ( m1_subset_1 @
% 0.42/0.60                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.42/0.60                   ( ![E:$i]:
% 0.42/0.60                     ( ( m1_subset_1 @ E @ A ) =>
% 0.42/0.60                       ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.42/0.60                         ( ?[F:$i]:
% 0.42/0.60                           ( ( r2_hidden @ F @ B ) & 
% 0.42/0.60                             ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.42/0.60                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i]:
% 0.42/0.60        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.42/0.60          ( ![B:$i]:
% 0.42/0.60            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.42/0.60              ( ![C:$i]:
% 0.42/0.60                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.42/0.60                  ( ![D:$i]:
% 0.42/0.60                    ( ( m1_subset_1 @
% 0.42/0.60                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.42/0.60                      ( ![E:$i]:
% 0.42/0.60                        ( ( m1_subset_1 @ E @ A ) =>
% 0.42/0.60                          ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.42/0.60                            ( ?[F:$i]:
% 0.42/0.60                              ( ( r2_hidden @ F @ B ) & 
% 0.42/0.60                                ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.42/0.60                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t53_relset_1])).
% 0.42/0.60  thf('0', plain,
% 0.42/0.60      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)
% 0.42/0.60        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)) | 
% 0.42/0.60       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.42/0.60      inference('split', [status(esa)], ['0'])).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      (((m1_subset_1 @ sk_F @ sk_C)
% 0.42/0.60        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (((m1_subset_1 @ sk_F @ sk_C)) | 
% 0.42/0.60       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.42/0.60      inference('split', [status(esa)], ['2'])).
% 0.42/0.60  thf('4', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(cc2_relset_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.42/0.60  thf('5', plain,
% 0.42/0.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.42/0.60         ((v5_relat_1 @ X21 @ X23)
% 0.42/0.60          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.42/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.60  thf('6', plain, ((v5_relat_1 @ sk_D_2 @ sk_C)),
% 0.42/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(redefinition_k8_relset_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.42/0.60  thf('8', plain,
% 0.42/0.60      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.42/0.60          | ((k8_relset_1 @ X25 @ X26 @ X24 @ X27) = (k10_relat_1 @ X24 @ X27)))),
% 0.42/0.60      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.42/0.60  thf('9', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0)
% 0.42/0.60           = (k10_relat_1 @ sk_D_2 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      (((r2_hidden @ sk_F @ sk_B)
% 0.42/0.60        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))
% 0.42/0.60         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.42/0.60      inference('split', [status(esa)], ['10'])).
% 0.42/0.60  thf('12', plain,
% 0.42/0.60      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.42/0.60         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.42/0.60      inference('sup+', [status(thm)], ['9', '11'])).
% 0.42/0.60  thf(t166_relat_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ C ) =>
% 0.42/0.60       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.42/0.60         ( ?[D:$i]:
% 0.42/0.60           ( ( r2_hidden @ D @ B ) & 
% 0.42/0.60             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.42/0.60             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X16 @ (k10_relat_1 @ X17 @ X15))
% 0.42/0.60          | (r2_hidden @ (sk_D_1 @ X17 @ X15 @ X16) @ (k2_relat_1 @ X17))
% 0.42/0.60          | ~ (v1_relat_1 @ X17))),
% 0.42/0.60      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.42/0.60  thf('14', plain,
% 0.42/0.60      (((~ (v1_relat_1 @ sk_D_2)
% 0.42/0.60         | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ 
% 0.42/0.60            (k2_relat_1 @ sk_D_2))))
% 0.42/0.60         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.42/0.60  thf('15', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(cc2_relat_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ A ) =>
% 0.42/0.60       ( ![B:$i]:
% 0.42/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.42/0.60  thf('16', plain,
% 0.42/0.60      (![X2 : $i, X3 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.42/0.60          | (v1_relat_1 @ X2)
% 0.42/0.60          | ~ (v1_relat_1 @ X3))),
% 0.42/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.42/0.60  thf('17', plain,
% 0.42/0.60      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_D_2))),
% 0.42/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.60  thf(fc6_relat_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.42/0.60  thf('18', plain,
% 0.42/0.60      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.42/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.42/0.60  thf('19', plain, ((v1_relat_1 @ sk_D_2)),
% 0.42/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.42/0.60  thf('20', plain,
% 0.42/0.60      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ (k2_relat_1 @ sk_D_2)))
% 0.42/0.60         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.42/0.60      inference('demod', [status(thm)], ['14', '19'])).
% 0.42/0.60  thf(t202_relat_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.42/0.60       ( ![C:$i]:
% 0.42/0.60         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.42/0.60  thf('21', plain,
% 0.42/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X18 @ (k2_relat_1 @ X19))
% 0.42/0.60          | (r2_hidden @ X18 @ X20)
% 0.42/0.60          | ~ (v5_relat_1 @ X19 @ X20)
% 0.42/0.60          | ~ (v1_relat_1 @ X19))),
% 0.42/0.60      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.42/0.60  thf('22', plain,
% 0.42/0.60      ((![X0 : $i]:
% 0.42/0.60          (~ (v1_relat_1 @ sk_D_2)
% 0.42/0.60           | ~ (v5_relat_1 @ sk_D_2 @ X0)
% 0.42/0.60           | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ X0)))
% 0.42/0.60         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.60  thf('23', plain, ((v1_relat_1 @ sk_D_2)),
% 0.42/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.42/0.60  thf('24', plain,
% 0.42/0.60      ((![X0 : $i]:
% 0.42/0.60          (~ (v5_relat_1 @ sk_D_2 @ X0)
% 0.42/0.60           | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ X0)))
% 0.42/0.60         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.42/0.60      inference('demod', [status(thm)], ['22', '23'])).
% 0.42/0.60  thf('25', plain,
% 0.42/0.60      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C))
% 0.42/0.60         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['6', '24'])).
% 0.42/0.60  thf(t1_subset, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.42/0.60  thf('26', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [t1_subset])).
% 0.42/0.60  thf('27', plain,
% 0.42/0.60      (((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C))
% 0.42/0.60         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.42/0.60  thf('28', plain,
% 0.42/0.60      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.42/0.60         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.42/0.60      inference('sup+', [status(thm)], ['9', '11'])).
% 0.42/0.60  thf('29', plain,
% 0.42/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X16 @ (k10_relat_1 @ X17 @ X15))
% 0.42/0.60          | (r2_hidden @ (k4_tarski @ X16 @ (sk_D_1 @ X17 @ X15 @ X16)) @ X17)
% 0.42/0.60          | ~ (v1_relat_1 @ X17))),
% 0.42/0.60      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.42/0.60  thf('30', plain,
% 0.42/0.60      (((~ (v1_relat_1 @ sk_D_2)
% 0.42/0.60         | (r2_hidden @ 
% 0.42/0.60            (k4_tarski @ sk_E_2 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2)) @ sk_D_2)))
% 0.42/0.60         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.42/0.60  thf('31', plain, ((v1_relat_1 @ sk_D_2)),
% 0.42/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.42/0.60  thf('32', plain,
% 0.42/0.60      (((r2_hidden @ 
% 0.42/0.60         (k4_tarski @ sk_E_2 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2)) @ sk_D_2))
% 0.42/0.60         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.42/0.60      inference('demod', [status(thm)], ['30', '31'])).
% 0.42/0.60  thf('33', plain,
% 0.42/0.60      (![X28 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X28 @ sk_C)
% 0.42/0.60          | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X28) @ sk_D_2)
% 0.42/0.60          | ~ (r2_hidden @ X28 @ sk_B)
% 0.42/0.60          | ~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('34', plain,
% 0.42/0.60      ((![X28 : $i]:
% 0.42/0.60          (~ (m1_subset_1 @ X28 @ sk_C)
% 0.42/0.60           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X28) @ sk_D_2)
% 0.42/0.60           | ~ (r2_hidden @ X28 @ sk_B)))
% 0.42/0.60         <= ((![X28 : $i]:
% 0.42/0.60                (~ (m1_subset_1 @ X28 @ sk_C)
% 0.42/0.60                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X28) @ sk_D_2)
% 0.42/0.60                 | ~ (r2_hidden @ X28 @ sk_B))))),
% 0.42/0.60      inference('split', [status(esa)], ['33'])).
% 0.42/0.60  thf('35', plain,
% 0.42/0.60      (((~ (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B)
% 0.42/0.60         | ~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C)))
% 0.42/0.60         <= ((![X28 : $i]:
% 0.42/0.60                (~ (m1_subset_1 @ X28 @ sk_C)
% 0.42/0.60                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X28) @ sk_D_2)
% 0.42/0.60                 | ~ (r2_hidden @ X28 @ sk_B))) & 
% 0.42/0.60             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['32', '34'])).
% 0.42/0.60  thf('36', plain,
% 0.42/0.60      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.42/0.60         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.42/0.60      inference('sup+', [status(thm)], ['9', '11'])).
% 0.42/0.60  thf('37', plain,
% 0.42/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X16 @ (k10_relat_1 @ X17 @ X15))
% 0.42/0.60          | (r2_hidden @ (sk_D_1 @ X17 @ X15 @ X16) @ X15)
% 0.42/0.60          | ~ (v1_relat_1 @ X17))),
% 0.42/0.60      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.42/0.60  thf('38', plain,
% 0.42/0.60      (((~ (v1_relat_1 @ sk_D_2)
% 0.42/0.60         | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B)))
% 0.42/0.60         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.42/0.60  thf('39', plain, ((v1_relat_1 @ sk_D_2)),
% 0.42/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.42/0.60  thf('40', plain,
% 0.42/0.60      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B))
% 0.42/0.60         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.42/0.60      inference('demod', [status(thm)], ['38', '39'])).
% 0.42/0.60  thf('41', plain,
% 0.42/0.60      ((~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C))
% 0.42/0.60         <= ((![X28 : $i]:
% 0.42/0.60                (~ (m1_subset_1 @ X28 @ sk_C)
% 0.42/0.60                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X28) @ sk_D_2)
% 0.42/0.60                 | ~ (r2_hidden @ X28 @ sk_B))) & 
% 0.42/0.60             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.42/0.60      inference('demod', [status(thm)], ['35', '40'])).
% 0.42/0.60  thf('42', plain,
% 0.42/0.60      (~ ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))) | 
% 0.42/0.60       ~
% 0.42/0.60       (![X28 : $i]:
% 0.42/0.60          (~ (m1_subset_1 @ X28 @ sk_C)
% 0.42/0.60           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X28) @ sk_D_2)
% 0.42/0.60           | ~ (r2_hidden @ X28 @ sk_B)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['27', '41'])).
% 0.42/0.60  thf('43', plain,
% 0.42/0.60      (((m1_subset_1 @ sk_F @ sk_C)) <= (((m1_subset_1 @ sk_F @ sk_C)))),
% 0.42/0.60      inference('split', [status(esa)], ['2'])).
% 0.42/0.60  thf('44', plain,
% 0.42/0.60      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.42/0.60      inference('split', [status(esa)], ['10'])).
% 0.42/0.60  thf('45', plain,
% 0.42/0.60      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2))
% 0.42/0.60         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.42/0.60      inference('split', [status(esa)], ['0'])).
% 0.42/0.60  thf('46', plain,
% 0.42/0.60      ((![X28 : $i]:
% 0.42/0.60          (~ (m1_subset_1 @ X28 @ sk_C)
% 0.42/0.60           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X28) @ sk_D_2)
% 0.42/0.60           | ~ (r2_hidden @ X28 @ sk_B)))
% 0.42/0.60         <= ((![X28 : $i]:
% 0.42/0.60                (~ (m1_subset_1 @ X28 @ sk_C)
% 0.42/0.60                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X28) @ sk_D_2)
% 0.42/0.60                 | ~ (r2_hidden @ X28 @ sk_B))))),
% 0.42/0.60      inference('split', [status(esa)], ['33'])).
% 0.42/0.60  thf('47', plain,
% 0.42/0.60      (((~ (r2_hidden @ sk_F @ sk_B) | ~ (m1_subset_1 @ sk_F @ sk_C)))
% 0.42/0.60         <= ((![X28 : $i]:
% 0.42/0.60                (~ (m1_subset_1 @ X28 @ sk_C)
% 0.42/0.60                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X28) @ sk_D_2)
% 0.42/0.60                 | ~ (r2_hidden @ X28 @ sk_B))) & 
% 0.42/0.60             ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['45', '46'])).
% 0.42/0.60  thf('48', plain,
% 0.42/0.60      ((~ (m1_subset_1 @ sk_F @ sk_C))
% 0.42/0.60         <= ((![X28 : $i]:
% 0.42/0.60                (~ (m1_subset_1 @ X28 @ sk_C)
% 0.42/0.60                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X28) @ sk_D_2)
% 0.42/0.60                 | ~ (r2_hidden @ X28 @ sk_B))) & 
% 0.42/0.60             ((r2_hidden @ sk_F @ sk_B)) & 
% 0.42/0.60             ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['44', '47'])).
% 0.42/0.60  thf('49', plain,
% 0.42/0.60      (~ ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)) | 
% 0.42/0.60       ~
% 0.42/0.60       (![X28 : $i]:
% 0.42/0.60          (~ (m1_subset_1 @ X28 @ sk_C)
% 0.42/0.60           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X28) @ sk_D_2)
% 0.42/0.60           | ~ (r2_hidden @ X28 @ sk_B))) | 
% 0.42/0.60       ~ ((m1_subset_1 @ sk_F @ sk_C)) | ~ ((r2_hidden @ sk_F @ sk_B))),
% 0.42/0.60      inference('sup-', [status(thm)], ['43', '48'])).
% 0.42/0.60  thf('50', plain,
% 0.42/0.60      (~ ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))) | 
% 0.42/0.60       (![X28 : $i]:
% 0.42/0.60          (~ (m1_subset_1 @ X28 @ sk_C)
% 0.42/0.60           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X28) @ sk_D_2)
% 0.42/0.60           | ~ (r2_hidden @ X28 @ sk_B)))),
% 0.42/0.60      inference('split', [status(esa)], ['33'])).
% 0.42/0.60  thf('51', plain,
% 0.42/0.60      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.42/0.60       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.42/0.60      inference('split', [status(esa)], ['10'])).
% 0.42/0.60  thf('52', plain,
% 0.42/0.60      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.42/0.60      inference('split', [status(esa)], ['10'])).
% 0.42/0.60  thf('53', plain,
% 0.42/0.60      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2))
% 0.42/0.60         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.42/0.60      inference('split', [status(esa)], ['0'])).
% 0.42/0.60  thf(d14_relat_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ A ) =>
% 0.42/0.60       ( ![B:$i,C:$i]:
% 0.42/0.60         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.42/0.60           ( ![D:$i]:
% 0.42/0.60             ( ( r2_hidden @ D @ C ) <=>
% 0.42/0.60               ( ?[E:$i]:
% 0.42/0.60                 ( ( r2_hidden @ E @ B ) & 
% 0.42/0.60                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.42/0.60  thf('54', plain,
% 0.42/0.60      (![X5 : $i, X6 : $i, X8 : $i, X10 : $i, X11 : $i]:
% 0.42/0.60         (((X8) != (k10_relat_1 @ X6 @ X5))
% 0.42/0.60          | (r2_hidden @ X10 @ X8)
% 0.42/0.60          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X6)
% 0.42/0.60          | ~ (r2_hidden @ X11 @ X5)
% 0.42/0.60          | ~ (v1_relat_1 @ X6))),
% 0.42/0.60      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.42/0.60  thf('55', plain,
% 0.42/0.60      (![X5 : $i, X6 : $i, X10 : $i, X11 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X6)
% 0.42/0.60          | ~ (r2_hidden @ X11 @ X5)
% 0.42/0.60          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X6)
% 0.42/0.60          | (r2_hidden @ X10 @ (k10_relat_1 @ X6 @ X5)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['54'])).
% 0.42/0.60  thf('56', plain,
% 0.42/0.60      ((![X0 : $i]:
% 0.42/0.60          ((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ X0))
% 0.42/0.60           | ~ (r2_hidden @ sk_F @ X0)
% 0.42/0.60           | ~ (v1_relat_1 @ sk_D_2)))
% 0.42/0.60         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['53', '55'])).
% 0.42/0.60  thf('57', plain, ((v1_relat_1 @ sk_D_2)),
% 0.42/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.42/0.60  thf('58', plain,
% 0.42/0.60      ((![X0 : $i]:
% 0.42/0.60          ((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ X0))
% 0.42/0.60           | ~ (r2_hidden @ sk_F @ X0)))
% 0.42/0.60         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.42/0.60      inference('demod', [status(thm)], ['56', '57'])).
% 0.42/0.60  thf('59', plain,
% 0.42/0.60      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.42/0.60         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.42/0.60             ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['52', '58'])).
% 0.42/0.60  thf('60', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0)
% 0.42/0.60           = (k10_relat_1 @ sk_D_2 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.42/0.60  thf('61', plain,
% 0.42/0.60      ((~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))
% 0.42/0.60         <= (~
% 0.42/0.60             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.42/0.60      inference('split', [status(esa)], ['33'])).
% 0.42/0.60  thf('62', plain,
% 0.42/0.60      ((~ (r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.42/0.60         <= (~
% 0.42/0.60             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.42/0.60  thf('63', plain,
% 0.42/0.60      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 0.42/0.60       ~ ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)) | 
% 0.42/0.60       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['59', '62'])).
% 0.42/0.60  thf('64', plain, ($false),
% 0.42/0.60      inference('sat_resolution*', [status(thm)],
% 0.42/0.60                ['1', '3', '42', '49', '50', '51', '63'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
