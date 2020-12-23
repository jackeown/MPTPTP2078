%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q2tuD3g307

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 161 expanded)
%              Number of leaves         :   27 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  788 (2430 expanded)
%              Number of equality atoms :    9 (  17 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

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
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X29 ) @ sk_D_2 )
      | ~ ( r2_hidden @ X29 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X29 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X29 @ sk_B ) )
    | ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k8_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k10_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0 )
      = ( k10_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k10_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_D_1 @ X18 @ X16 @ X17 ) ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) ) @ sk_D_2 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) ) @ sk_D_2 )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X29 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X29 @ sk_B ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X29 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('19',plain,
    ( ( ~ ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X29 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X29 @ sk_B ) )
      & ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k10_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( sk_D_1 @ X18 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('22',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('24',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('26',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k10_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( sk_D_1 @ X18 @ X16 @ X17 ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('27',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ ( k2_relat_1 @ sk_D_2 ) ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('29',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ ( k2_relat_1 @ sk_D_2 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X19 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('32',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_C @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('34',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(demod,[status(thm)],['32','35'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( m1_subset_1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,
    ( ~ ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X29 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X29 @ sk_B ) )
    | ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','24','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('42',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('43',plain,
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

thf('44',plain,(
    ! [X6: $i,X7: $i,X9: $i,X11: $i,X12: $i] :
      ( ( X9
       != ( k10_relat_1 @ X7 @ X6 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X7 )
      | ~ ( r2_hidden @ X12 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('45',plain,(
    ! [X6: $i,X7: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( r2_hidden @ X12 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X7 )
      | ( r2_hidden @ X11 @ ( k10_relat_1 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 )
        | ~ ( v1_relat_1 @ sk_D_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0 )
      = ( k10_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','40','41','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q2tuD3g307
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 66 iterations in 0.072s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.53  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.21/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.53  thf(t53_relset_1, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.53               ( ![D:$i]:
% 0.21/0.53                 ( ( m1_subset_1 @
% 0.21/0.53                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.21/0.53                   ( ![E:$i]:
% 0.21/0.53                     ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.53                       ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.21/0.53                         ( ?[F:$i]:
% 0.21/0.53                           ( ( r2_hidden @ F @ B ) & 
% 0.21/0.53                             ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.21/0.53                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.53              ( ![C:$i]:
% 0.21/0.53                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.53                  ( ![D:$i]:
% 0.21/0.53                    ( ( m1_subset_1 @
% 0.21/0.53                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.21/0.53                      ( ![E:$i]:
% 0.21/0.53                        ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.53                          ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.21/0.53                            ( ?[F:$i]:
% 0.21/0.53                              ( ( r2_hidden @ F @ B ) & 
% 0.21/0.53                                ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.21/0.53                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t53_relset_1])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)
% 0.21/0.53        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)) | 
% 0.21/0.53       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X29 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X29 @ sk_C)
% 0.21/0.53          | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X29) @ sk_D_2)
% 0.21/0.53          | ~ (r2_hidden @ X29 @ sk_B)
% 0.21/0.53          | ~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      ((![X29 : $i]:
% 0.21/0.53          (~ (m1_subset_1 @ X29 @ sk_C)
% 0.21/0.53           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X29) @ sk_D_2)
% 0.21/0.53           | ~ (r2_hidden @ X29 @ sk_B))) | 
% 0.21/0.53       ~ ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.21/0.53      inference('split', [status(esa)], ['2'])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.21/0.53          | ((k8_relset_1 @ X26 @ X27 @ X25 @ X28) = (k10_relat_1 @ X25 @ X28)))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0)
% 0.21/0.53           = (k10_relat_1 @ sk_D_2 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (((r2_hidden @ sk_F @ sk_B)
% 0.21/0.53        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))
% 0.21/0.53         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.21/0.53      inference('split', [status(esa)], ['7'])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.21/0.53         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['6', '8'])).
% 0.21/0.53  thf(t166_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ C ) =>
% 0.21/0.53       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.21/0.53         ( ?[D:$i]:
% 0.21/0.53           ( ( r2_hidden @ D @ B ) & 
% 0.21/0.53             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.21/0.53             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X17 @ (k10_relat_1 @ X18 @ X16))
% 0.21/0.53          | (r2_hidden @ (k4_tarski @ X17 @ (sk_D_1 @ X18 @ X16 @ X17)) @ X18)
% 0.21/0.53          | ~ (v1_relat_1 @ X18))),
% 0.21/0.53      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (((~ (v1_relat_1 @ sk_D_2)
% 0.21/0.53         | (r2_hidden @ 
% 0.21/0.53            (k4_tarski @ sk_E_2 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2)) @ sk_D_2)))
% 0.21/0.53         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc2_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X3 : $i, X4 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.21/0.53          | (v1_relat_1 @ X3)
% 0.21/0.53          | ~ (v1_relat_1 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_D_2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf(fc6_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.53  thf('16', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (((r2_hidden @ 
% 0.21/0.53         (k4_tarski @ sk_E_2 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2)) @ sk_D_2))
% 0.21/0.53         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.21/0.53      inference('demod', [status(thm)], ['11', '16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      ((![X29 : $i]:
% 0.21/0.53          (~ (m1_subset_1 @ X29 @ sk_C)
% 0.21/0.53           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X29) @ sk_D_2)
% 0.21/0.53           | ~ (r2_hidden @ X29 @ sk_B)))
% 0.21/0.53         <= ((![X29 : $i]:
% 0.21/0.53                (~ (m1_subset_1 @ X29 @ sk_C)
% 0.21/0.53                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X29) @ sk_D_2)
% 0.21/0.53                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.21/0.53      inference('split', [status(esa)], ['2'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (((~ (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B)
% 0.21/0.53         | ~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C)))
% 0.21/0.53         <= ((![X29 : $i]:
% 0.21/0.53                (~ (m1_subset_1 @ X29 @ sk_C)
% 0.21/0.53                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X29) @ sk_D_2)
% 0.21/0.53                 | ~ (r2_hidden @ X29 @ sk_B))) & 
% 0.21/0.53             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.21/0.53         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['6', '8'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X17 @ (k10_relat_1 @ X18 @ X16))
% 0.21/0.53          | (r2_hidden @ (sk_D_1 @ X18 @ X16 @ X17) @ X16)
% 0.21/0.53          | ~ (v1_relat_1 @ X18))),
% 0.21/0.53      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (((~ (v1_relat_1 @ sk_D_2)
% 0.21/0.53         | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B)))
% 0.21/0.53         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.53  thf('23', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B))
% 0.21/0.53         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.21/0.53      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.21/0.53         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['6', '8'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X17 @ (k10_relat_1 @ X18 @ X16))
% 0.21/0.53          | (r2_hidden @ (sk_D_1 @ X18 @ X16 @ X17) @ (k2_relat_1 @ X18))
% 0.21/0.53          | ~ (v1_relat_1 @ X18))),
% 0.21/0.53      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (((~ (v1_relat_1 @ sk_D_2)
% 0.21/0.53         | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ 
% 0.21/0.53            (k2_relat_1 @ sk_D_2))))
% 0.21/0.53         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.53  thf('28', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ (k2_relat_1 @ sk_D_2)))
% 0.21/0.53         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.21/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_k2_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.53         ((m1_subset_1 @ (k2_relset_1 @ X19 @ X20 @ X21) @ (k1_zfmisc_1 @ X20))
% 0.21/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_C @ sk_D_2) @ 
% 0.21/0.53        (k1_zfmisc_1 @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.53         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.21/0.53          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (((k2_relset_1 @ sk_A @ sk_C @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ (k1_zfmisc_1 @ sk_C))),
% 0.21/0.53      inference('demod', [status(thm)], ['32', '35'])).
% 0.21/0.53  thf(t4_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.53       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.21/0.53          | (m1_subset_1 @ X0 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((m1_subset_1 @ X0 @ sk_C)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C))
% 0.21/0.53         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '38'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (~
% 0.21/0.53       (![X29 : $i]:
% 0.21/0.53          (~ (m1_subset_1 @ X29 @ sk_C)
% 0.21/0.53           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X29) @ sk_D_2)
% 0.21/0.53           | ~ (r2_hidden @ X29 @ sk_B))) | 
% 0.21/0.53       ~ ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['19', '24', '39'])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.21/0.53       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.21/0.53      inference('split', [status(esa)], ['7'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.21/0.53      inference('split', [status(esa)], ['7'])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2))
% 0.21/0.53         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf(d14_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i,C:$i]:
% 0.21/0.53         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.21/0.53           ( ![D:$i]:
% 0.21/0.53             ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.53               ( ?[E:$i]:
% 0.21/0.53                 ( ( r2_hidden @ E @ B ) & 
% 0.21/0.53                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i, X9 : $i, X11 : $i, X12 : $i]:
% 0.21/0.53         (((X9) != (k10_relat_1 @ X7 @ X6))
% 0.21/0.53          | (r2_hidden @ X11 @ X9)
% 0.21/0.53          | ~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X7)
% 0.21/0.53          | ~ (r2_hidden @ X12 @ X6)
% 0.21/0.53          | ~ (v1_relat_1 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i, X11 : $i, X12 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X7)
% 0.21/0.53          | ~ (r2_hidden @ X12 @ X6)
% 0.21/0.53          | ~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X7)
% 0.21/0.53          | (r2_hidden @ X11 @ (k10_relat_1 @ X7 @ X6)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          ((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ X0))
% 0.21/0.53           | ~ (r2_hidden @ sk_F @ X0)
% 0.21/0.53           | ~ (v1_relat_1 @ sk_D_2)))
% 0.21/0.53         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['43', '45'])).
% 0.21/0.53  thf('47', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          ((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ X0))
% 0.21/0.53           | ~ (r2_hidden @ sk_F @ X0)))
% 0.21/0.53         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.21/0.53      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.21/0.53         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.21/0.53             ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['42', '48'])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0)
% 0.21/0.53           = (k10_relat_1 @ sk_D_2 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      ((~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.21/0.53      inference('split', [status(esa)], ['2'])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      ((~ (r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.21/0.53         <= (~
% 0.21/0.53             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 0.21/0.53       ~ ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)) | 
% 0.21/0.53       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['49', '52'])).
% 0.21/0.53  thf('54', plain, ($false),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['1', '3', '40', '41', '53'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
