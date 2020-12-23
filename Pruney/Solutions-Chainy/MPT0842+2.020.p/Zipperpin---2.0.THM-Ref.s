%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tF7tt5KpX8

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 164 expanded)
%              Number of leaves         :   28 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  813 (2455 expanded)
%              Number of equality atoms :    9 (  17 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X31 ) @ sk_D_2 )
      | ~ ( r2_hidden @ X31 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X31 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X31 @ sk_B ) )
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k8_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k10_relat_1 @ X27 @ X30 ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k10_relat_1 @ X20 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_D_1 @ X20 @ X18 @ X19 ) ) @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) ) @ sk_D_2 )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,
    ( ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X31 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X31 @ sk_B ) )
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X31 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X31 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('19',plain,
    ( ( ~ ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C ) )
   <= ( ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X31 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X31 @ sk_B ) )
      & ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k10_relat_1 @ X20 @ X18 ) )
      | ( r2_hidden @ ( sk_D_1 @ X20 @ X18 @ X19 ) @ X18 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k10_relat_1 @ X20 @ X18 ) )
      | ( r2_hidden @ ( sk_D_1 @ X20 @ X18 @ X19 ) @ ( k2_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X21 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(demod,[status(thm)],['32','35'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('41',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X31 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X31 @ sk_B ) )
    | ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','24','41'])).

thf('43',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('44',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('45',plain,
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

thf('46',plain,(
    ! [X8: $i,X9: $i,X11: $i,X13: $i,X14: $i] :
      ( ( X11
       != ( k10_relat_1 @ X9 @ X8 ) )
      | ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X9 )
      | ~ ( r2_hidden @ X14 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('47',plain,(
    ! [X8: $i,X9: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( r2_hidden @ X14 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X9 )
      | ( r2_hidden @ X13 @ ( k10_relat_1 @ X9 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 )
        | ~ ( v1_relat_1 @ sk_D_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0 )
      = ( k10_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','42','43','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tF7tt5KpX8
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:07:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 102 iterations in 0.123s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.57  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.57  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.20/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.57  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.57  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.57  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.20/0.57  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.57  thf(t53_relset_1, conjecture,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.57           ( ![C:$i]:
% 0.20/0.57             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.57               ( ![D:$i]:
% 0.20/0.57                 ( ( m1_subset_1 @
% 0.20/0.57                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.20/0.57                   ( ![E:$i]:
% 0.20/0.57                     ( ( m1_subset_1 @ E @ A ) =>
% 0.20/0.57                       ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.20/0.57                         ( ?[F:$i]:
% 0.20/0.57                           ( ( r2_hidden @ F @ B ) & 
% 0.20/0.57                             ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.20/0.57                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i]:
% 0.20/0.57        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.57          ( ![B:$i]:
% 0.20/0.57            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.57              ( ![C:$i]:
% 0.20/0.57                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.57                  ( ![D:$i]:
% 0.20/0.57                    ( ( m1_subset_1 @
% 0.20/0.57                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.20/0.57                      ( ![E:$i]:
% 0.20/0.57                        ( ( m1_subset_1 @ E @ A ) =>
% 0.20/0.57                          ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.20/0.57                            ( ?[F:$i]:
% 0.20/0.57                              ( ( r2_hidden @ F @ B ) & 
% 0.20/0.57                                ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.20/0.57                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t53_relset_1])).
% 0.20/0.57  thf('0', plain,
% 0.20/0.57      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)
% 0.20/0.57        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('1', plain,
% 0.20/0.57      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)) | 
% 0.20/0.57       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.20/0.57      inference('split', [status(esa)], ['0'])).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (![X31 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X31 @ sk_C)
% 0.20/0.57          | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X31) @ sk_D_2)
% 0.20/0.57          | ~ (r2_hidden @ X31 @ sk_B)
% 0.20/0.57          | ~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      ((![X31 : $i]:
% 0.20/0.57          (~ (m1_subset_1 @ X31 @ sk_C)
% 0.20/0.57           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X31) @ sk_D_2)
% 0.20/0.57           | ~ (r2_hidden @ X31 @ sk_B))) | 
% 0.20/0.57       ~ ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.20/0.57      inference('split', [status(esa)], ['2'])).
% 0.20/0.57  thf('4', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.57       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.20/0.57          | ((k8_relset_1 @ X28 @ X29 @ X27 @ X30) = (k10_relat_1 @ X27 @ X30)))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0)
% 0.20/0.57           = (k10_relat_1 @ sk_D_2 @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      (((r2_hidden @ sk_F @ sk_B)
% 0.20/0.57        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('8', plain,
% 0.20/0.57      (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))
% 0.20/0.57         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.57      inference('split', [status(esa)], ['7'])).
% 0.20/0.57  thf('9', plain,
% 0.20/0.57      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.20/0.57         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.57      inference('sup+', [status(thm)], ['6', '8'])).
% 0.20/0.57  thf(t166_relat_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ C ) =>
% 0.20/0.57       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.20/0.57         ( ?[D:$i]:
% 0.20/0.57           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.57             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.20/0.57             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.57  thf('10', plain,
% 0.20/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X19 @ (k10_relat_1 @ X20 @ X18))
% 0.20/0.57          | (r2_hidden @ (k4_tarski @ X19 @ (sk_D_1 @ X20 @ X18 @ X19)) @ X20)
% 0.20/0.57          | ~ (v1_relat_1 @ X20))),
% 0.20/0.57      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.57  thf('11', plain,
% 0.20/0.57      (((~ (v1_relat_1 @ sk_D_2)
% 0.20/0.57         | (r2_hidden @ 
% 0.20/0.57            (k4_tarski @ sk_E_2 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2)) @ sk_D_2)))
% 0.20/0.57         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(cc2_relat_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ A ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.57  thf('13', plain,
% 0.20/0.57      (![X5 : $i, X6 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.20/0.57          | (v1_relat_1 @ X5)
% 0.20/0.57          | ~ (v1_relat_1 @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_D_2))),
% 0.20/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.57  thf(fc6_relat_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.20/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.57  thf('16', plain, ((v1_relat_1 @ sk_D_2)),
% 0.20/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      (((r2_hidden @ 
% 0.20/0.57         (k4_tarski @ sk_E_2 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2)) @ sk_D_2))
% 0.20/0.57         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.57      inference('demod', [status(thm)], ['11', '16'])).
% 0.20/0.57  thf('18', plain,
% 0.20/0.57      ((![X31 : $i]:
% 0.20/0.57          (~ (m1_subset_1 @ X31 @ sk_C)
% 0.20/0.57           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X31) @ sk_D_2)
% 0.20/0.57           | ~ (r2_hidden @ X31 @ sk_B)))
% 0.20/0.57         <= ((![X31 : $i]:
% 0.20/0.57                (~ (m1_subset_1 @ X31 @ sk_C)
% 0.20/0.57                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X31) @ sk_D_2)
% 0.20/0.57                 | ~ (r2_hidden @ X31 @ sk_B))))),
% 0.20/0.57      inference('split', [status(esa)], ['2'])).
% 0.20/0.57  thf('19', plain,
% 0.20/0.57      (((~ (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B)
% 0.20/0.57         | ~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C)))
% 0.20/0.57         <= ((![X31 : $i]:
% 0.20/0.57                (~ (m1_subset_1 @ X31 @ sk_C)
% 0.20/0.57                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X31) @ sk_D_2)
% 0.20/0.57                 | ~ (r2_hidden @ X31 @ sk_B))) & 
% 0.20/0.57             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.20/0.57         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.57      inference('sup+', [status(thm)], ['6', '8'])).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X19 @ (k10_relat_1 @ X20 @ X18))
% 0.20/0.57          | (r2_hidden @ (sk_D_1 @ X20 @ X18 @ X19) @ X18)
% 0.20/0.57          | ~ (v1_relat_1 @ X20))),
% 0.20/0.57      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.57  thf('22', plain,
% 0.20/0.57      (((~ (v1_relat_1 @ sk_D_2)
% 0.20/0.57         | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B)))
% 0.20/0.57         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.57  thf('23', plain, ((v1_relat_1 @ sk_D_2)),
% 0.20/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B))
% 0.20/0.57         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.57      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.57  thf('25', plain,
% 0.20/0.57      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.20/0.57         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.57      inference('sup+', [status(thm)], ['6', '8'])).
% 0.20/0.57  thf('26', plain,
% 0.20/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X19 @ (k10_relat_1 @ X20 @ X18))
% 0.20/0.57          | (r2_hidden @ (sk_D_1 @ X20 @ X18 @ X19) @ (k2_relat_1 @ X20))
% 0.20/0.57          | ~ (v1_relat_1 @ X20))),
% 0.20/0.57      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.57  thf('27', plain,
% 0.20/0.57      (((~ (v1_relat_1 @ sk_D_2)
% 0.20/0.57         | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ 
% 0.20/0.57            (k2_relat_1 @ sk_D_2))))
% 0.20/0.57         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.57  thf('28', plain, ((v1_relat_1 @ sk_D_2)),
% 0.20/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.57  thf('29', plain,
% 0.20/0.57      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ (k2_relat_1 @ sk_D_2)))
% 0.20/0.57         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.57      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.57  thf('30', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(dt_k2_relset_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.57       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.57  thf('31', plain,
% 0.20/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.57         ((m1_subset_1 @ (k2_relset_1 @ X21 @ X22 @ X23) @ (k1_zfmisc_1 @ X22))
% 0.20/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.20/0.57      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.20/0.57  thf('32', plain,
% 0.20/0.57      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_C @ sk_D_2) @ 
% 0.20/0.57        (k1_zfmisc_1 @ sk_C))),
% 0.20/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.57  thf('33', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.57  thf('34', plain,
% 0.20/0.57      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.57         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.20/0.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.57  thf('35', plain,
% 0.20/0.57      (((k2_relset_1 @ sk_A @ sk_C @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.20/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.57  thf('36', plain,
% 0.20/0.57      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ (k1_zfmisc_1 @ sk_C))),
% 0.20/0.57      inference('demod', [status(thm)], ['32', '35'])).
% 0.20/0.57  thf(l3_subset_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.57  thf('37', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.57          | (r2_hidden @ X0 @ X2)
% 0.20/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.57      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.57  thf('38', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((r2_hidden @ X0 @ sk_C) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.57  thf('39', plain,
% 0.20/0.57      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C))
% 0.20/0.57         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['29', '38'])).
% 0.20/0.57  thf(t1_subset, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.57  thf('40', plain,
% 0.20/0.57      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.20/0.57      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.57  thf('41', plain,
% 0.20/0.57      (((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C))
% 0.20/0.57         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.57  thf('42', plain,
% 0.20/0.57      (~
% 0.20/0.57       (![X31 : $i]:
% 0.20/0.57          (~ (m1_subset_1 @ X31 @ sk_C)
% 0.20/0.57           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X31) @ sk_D_2)
% 0.20/0.57           | ~ (r2_hidden @ X31 @ sk_B))) | 
% 0.20/0.57       ~ ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['19', '24', '41'])).
% 0.20/0.57  thf('43', plain,
% 0.20/0.57      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.20/0.57       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.20/0.57      inference('split', [status(esa)], ['7'])).
% 0.20/0.57  thf('44', plain,
% 0.20/0.57      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.20/0.57      inference('split', [status(esa)], ['7'])).
% 0.20/0.57  thf('45', plain,
% 0.20/0.57      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2))
% 0.20/0.57         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.20/0.57      inference('split', [status(esa)], ['0'])).
% 0.20/0.57  thf(d14_relat_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ A ) =>
% 0.20/0.57       ( ![B:$i,C:$i]:
% 0.20/0.57         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.20/0.57           ( ![D:$i]:
% 0.20/0.57             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.57               ( ?[E:$i]:
% 0.20/0.57                 ( ( r2_hidden @ E @ B ) & 
% 0.20/0.57                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.20/0.57  thf('46', plain,
% 0.20/0.57      (![X8 : $i, X9 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 0.20/0.57         (((X11) != (k10_relat_1 @ X9 @ X8))
% 0.20/0.57          | (r2_hidden @ X13 @ X11)
% 0.20/0.57          | ~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X9)
% 0.20/0.57          | ~ (r2_hidden @ X14 @ X8)
% 0.20/0.57          | ~ (v1_relat_1 @ X9))),
% 0.20/0.57      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.20/0.57  thf('47', plain,
% 0.20/0.57      (![X8 : $i, X9 : $i, X13 : $i, X14 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ X9)
% 0.20/0.57          | ~ (r2_hidden @ X14 @ X8)
% 0.20/0.57          | ~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X9)
% 0.20/0.57          | (r2_hidden @ X13 @ (k10_relat_1 @ X9 @ X8)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.57  thf('48', plain,
% 0.20/0.57      ((![X0 : $i]:
% 0.20/0.57          ((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ X0))
% 0.20/0.57           | ~ (r2_hidden @ sk_F @ X0)
% 0.20/0.57           | ~ (v1_relat_1 @ sk_D_2)))
% 0.20/0.57         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['45', '47'])).
% 0.20/0.57  thf('49', plain, ((v1_relat_1 @ sk_D_2)),
% 0.20/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.57  thf('50', plain,
% 0.20/0.57      ((![X0 : $i]:
% 0.20/0.57          ((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ X0))
% 0.20/0.57           | ~ (r2_hidden @ sk_F @ X0)))
% 0.20/0.57         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.20/0.57      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.57  thf('51', plain,
% 0.20/0.57      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.20/0.57         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.20/0.57             ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['44', '50'])).
% 0.20/0.57  thf('52', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0)
% 0.20/0.57           = (k10_relat_1 @ sk_D_2 @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.57  thf('53', plain,
% 0.20/0.57      ((~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))
% 0.20/0.57         <= (~
% 0.20/0.57             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.57      inference('split', [status(esa)], ['2'])).
% 0.20/0.57  thf('54', plain,
% 0.20/0.57      ((~ (r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.20/0.57         <= (~
% 0.20/0.57             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.57  thf('55', plain,
% 0.20/0.57      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 0.20/0.57       ~ ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)) | 
% 0.20/0.57       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['51', '54'])).
% 0.20/0.57  thf('56', plain, ($false),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['1', '3', '42', '43', '55'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
