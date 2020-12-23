%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eJzZ4r49cJ

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:25 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 175 expanded)
%              Number of leaves         :   27 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  929 (2909 expanded)
%              Number of equality atoms :    9 (  17 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k8_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k10_relat_1 @ X26 @ X29 ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k10_relat_1 @ X16 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ X15 @ ( sk_D_1 @ X16 @ X14 @ X15 ) ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) ) @ sk_D_2 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
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
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) ) @ sk_D_2 )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X30 ) @ sk_D_2 )
      | ~ ( r2_hidden @ X30 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X30 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X30 @ sk_B ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X30 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X30 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( ~ ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C ) )
   <= ( ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X30 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X30 @ sk_B ) )
      & ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k10_relat_1 @ X16 @ X14 ) )
      | ( r2_hidden @ ( sk_D_1 @ X16 @ X14 @ X15 ) @ X14 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('21',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k10_relat_1 @ X16 @ X14 ) )
      | ( r2_hidden @ ( sk_D_1 @ X16 @ X14 @ X15 ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('26',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ ( k2_relat_1 @ sk_D_2 ) ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ ( k2_relat_1 @ sk_D_2 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X20 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('31',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_C @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('34',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(demod,[status(thm)],['31','34'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('40',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) )
    | ~ ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X30 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X30 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','23','40'])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
   <= ( m1_subset_1 @ sk_F @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('43',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('44',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X30 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X30 @ sk_B ) )
   <= ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X30 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X30 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('46',plain,
    ( ( ~ ( r2_hidden @ sk_F @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ sk_C ) )
   <= ( ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X30 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X30 @ sk_B ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( m1_subset_1 @ sk_F @ sk_C )
   <= ( ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X30 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X30 @ sk_B ) )
      & ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 )
    | ~ ! [X30: $i] :
          ( ~ ( m1_subset_1 @ X30 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X30 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X30 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F @ sk_C )
    | ~ ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) )
    | ! [X30: $i] :
        ( ~ ( m1_subset_1 @ X30 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ X30 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X30 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('50',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('51',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('52',plain,
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

thf('53',plain,(
    ! [X6: $i,X7: $i,X9: $i,X11: $i,X12: $i] :
      ( ( X9
       != ( k10_relat_1 @ X7 @ X6 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X7 )
      | ~ ( r2_hidden @ X12 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('54',plain,(
    ! [X6: $i,X7: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( r2_hidden @ X12 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X7 )
      | ( r2_hidden @ X11 @ ( k10_relat_1 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 )
        | ~ ( v1_relat_1 @ sk_D_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0 )
      = ( k10_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('60',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('61',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k10_relat_1 @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_F ) @ sk_D_2 )
    | ( r2_hidden @ sk_E_2 @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','41','48','49','50','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eJzZ4r49cJ
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:11:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.68  % Solved by: fo/fo7.sh
% 0.49/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.68  % done 173 iterations in 0.227s
% 0.49/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.68  % SZS output start Refutation
% 0.49/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.68  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.49/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.68  thf(sk_F_type, type, sk_F: $i).
% 0.49/0.68  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.49/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.49/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.68  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.49/0.68  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.49/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.68  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.49/0.68  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.49/0.68  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.49/0.68  thf(t53_relset_1, conjecture,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.49/0.68           ( ![C:$i]:
% 0.49/0.68             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.49/0.68               ( ![D:$i]:
% 0.49/0.68                 ( ( m1_subset_1 @
% 0.49/0.68                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.49/0.68                   ( ![E:$i]:
% 0.49/0.68                     ( ( m1_subset_1 @ E @ A ) =>
% 0.49/0.68                       ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.49/0.68                         ( ?[F:$i]:
% 0.49/0.68                           ( ( r2_hidden @ F @ B ) & 
% 0.49/0.68                             ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.49/0.68                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.49/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.68    (~( ![A:$i]:
% 0.49/0.68        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.49/0.68          ( ![B:$i]:
% 0.49/0.68            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.49/0.68              ( ![C:$i]:
% 0.49/0.68                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.49/0.68                  ( ![D:$i]:
% 0.49/0.68                    ( ( m1_subset_1 @
% 0.49/0.68                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.49/0.68                      ( ![E:$i]:
% 0.49/0.68                        ( ( m1_subset_1 @ E @ A ) =>
% 0.49/0.68                          ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.49/0.68                            ( ?[F:$i]:
% 0.49/0.68                              ( ( r2_hidden @ F @ B ) & 
% 0.49/0.68                                ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.49/0.68                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.49/0.68    inference('cnf.neg', [status(esa)], [t53_relset_1])).
% 0.49/0.68  thf('0', plain,
% 0.49/0.68      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)
% 0.49/0.68        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('1', plain,
% 0.49/0.68      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)) | 
% 0.49/0.68       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.49/0.68      inference('split', [status(esa)], ['0'])).
% 0.49/0.68  thf('2', plain,
% 0.49/0.68      (((m1_subset_1 @ sk_F @ sk_C)
% 0.49/0.68        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('3', plain,
% 0.49/0.68      (((m1_subset_1 @ sk_F @ sk_C)) | 
% 0.49/0.68       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.49/0.68      inference('split', [status(esa)], ['2'])).
% 0.49/0.68  thf('4', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(redefinition_k8_relset_1, axiom,
% 0.49/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.68       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.49/0.68  thf('5', plain,
% 0.49/0.68      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.49/0.68          | ((k8_relset_1 @ X27 @ X28 @ X26 @ X29) = (k10_relat_1 @ X26 @ X29)))),
% 0.49/0.68      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.49/0.68  thf('6', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0)
% 0.49/0.68           = (k10_relat_1 @ sk_D_2 @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['4', '5'])).
% 0.49/0.68  thf('7', plain,
% 0.49/0.68      (((r2_hidden @ sk_F @ sk_B)
% 0.49/0.68        | (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('8', plain,
% 0.49/0.68      (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))
% 0.49/0.68         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.49/0.68      inference('split', [status(esa)], ['7'])).
% 0.49/0.68  thf('9', plain,
% 0.49/0.68      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.49/0.68         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.49/0.68      inference('sup+', [status(thm)], ['6', '8'])).
% 0.49/0.68  thf(t166_relat_1, axiom,
% 0.49/0.68    (![A:$i,B:$i,C:$i]:
% 0.49/0.68     ( ( v1_relat_1 @ C ) =>
% 0.49/0.68       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.49/0.68         ( ?[D:$i]:
% 0.49/0.68           ( ( r2_hidden @ D @ B ) & 
% 0.49/0.68             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.49/0.68             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.49/0.68  thf('10', plain,
% 0.49/0.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.68         (~ (r2_hidden @ X15 @ (k10_relat_1 @ X16 @ X14))
% 0.49/0.68          | (r2_hidden @ (k4_tarski @ X15 @ (sk_D_1 @ X16 @ X14 @ X15)) @ X16)
% 0.49/0.68          | ~ (v1_relat_1 @ X16))),
% 0.49/0.68      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.49/0.68  thf('11', plain,
% 0.49/0.68      (((~ (v1_relat_1 @ sk_D_2)
% 0.49/0.68         | (r2_hidden @ 
% 0.49/0.68            (k4_tarski @ sk_E_2 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2)) @ sk_D_2)))
% 0.49/0.68         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['9', '10'])).
% 0.49/0.68  thf('12', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(cc1_relset_1, axiom,
% 0.49/0.68    (![A:$i,B:$i,C:$i]:
% 0.49/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.68       ( v1_relat_1 @ C ) ))).
% 0.49/0.68  thf('13', plain,
% 0.49/0.68      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.49/0.68         ((v1_relat_1 @ X17)
% 0.49/0.68          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.49/0.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.49/0.68  thf('14', plain, ((v1_relat_1 @ sk_D_2)),
% 0.49/0.68      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.68  thf('15', plain,
% 0.49/0.68      (((r2_hidden @ 
% 0.49/0.68         (k4_tarski @ sk_E_2 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2)) @ sk_D_2))
% 0.49/0.68         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.49/0.68      inference('demod', [status(thm)], ['11', '14'])).
% 0.49/0.68  thf('16', plain,
% 0.49/0.68      (![X30 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X30 @ sk_C)
% 0.49/0.68          | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X30) @ sk_D_2)
% 0.49/0.68          | ~ (r2_hidden @ X30 @ sk_B)
% 0.49/0.68          | ~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('17', plain,
% 0.49/0.68      ((![X30 : $i]:
% 0.49/0.68          (~ (m1_subset_1 @ X30 @ sk_C)
% 0.49/0.68           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X30) @ sk_D_2)
% 0.49/0.68           | ~ (r2_hidden @ X30 @ sk_B)))
% 0.49/0.68         <= ((![X30 : $i]:
% 0.49/0.68                (~ (m1_subset_1 @ X30 @ sk_C)
% 0.49/0.68                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X30) @ sk_D_2)
% 0.49/0.68                 | ~ (r2_hidden @ X30 @ sk_B))))),
% 0.49/0.68      inference('split', [status(esa)], ['16'])).
% 0.49/0.68  thf('18', plain,
% 0.49/0.68      (((~ (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B)
% 0.49/0.68         | ~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C)))
% 0.49/0.68         <= ((![X30 : $i]:
% 0.49/0.68                (~ (m1_subset_1 @ X30 @ sk_C)
% 0.49/0.68                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X30) @ sk_D_2)
% 0.49/0.68                 | ~ (r2_hidden @ X30 @ sk_B))) & 
% 0.49/0.68             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['15', '17'])).
% 0.49/0.68  thf('19', plain,
% 0.49/0.68      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.49/0.68         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.49/0.68      inference('sup+', [status(thm)], ['6', '8'])).
% 0.49/0.68  thf('20', plain,
% 0.49/0.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.68         (~ (r2_hidden @ X15 @ (k10_relat_1 @ X16 @ X14))
% 0.49/0.68          | (r2_hidden @ (sk_D_1 @ X16 @ X14 @ X15) @ X14)
% 0.49/0.68          | ~ (v1_relat_1 @ X16))),
% 0.49/0.68      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.49/0.68  thf('21', plain,
% 0.49/0.68      (((~ (v1_relat_1 @ sk_D_2)
% 0.49/0.68         | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B)))
% 0.49/0.68         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.49/0.68  thf('22', plain, ((v1_relat_1 @ sk_D_2)),
% 0.49/0.68      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.68  thf('23', plain,
% 0.49/0.68      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B))
% 0.49/0.68         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.49/0.68      inference('demod', [status(thm)], ['21', '22'])).
% 0.49/0.68  thf('24', plain,
% 0.49/0.68      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.49/0.68         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.49/0.68      inference('sup+', [status(thm)], ['6', '8'])).
% 0.49/0.68  thf('25', plain,
% 0.49/0.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.68         (~ (r2_hidden @ X15 @ (k10_relat_1 @ X16 @ X14))
% 0.49/0.68          | (r2_hidden @ (sk_D_1 @ X16 @ X14 @ X15) @ (k2_relat_1 @ X16))
% 0.49/0.68          | ~ (v1_relat_1 @ X16))),
% 0.49/0.68      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.49/0.68  thf('26', plain,
% 0.49/0.68      (((~ (v1_relat_1 @ sk_D_2)
% 0.49/0.68         | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ 
% 0.49/0.68            (k2_relat_1 @ sk_D_2))))
% 0.49/0.68         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['24', '25'])).
% 0.49/0.68  thf('27', plain, ((v1_relat_1 @ sk_D_2)),
% 0.49/0.68      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.68  thf('28', plain,
% 0.49/0.68      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ (k2_relat_1 @ sk_D_2)))
% 0.49/0.68         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.49/0.68      inference('demod', [status(thm)], ['26', '27'])).
% 0.49/0.68  thf('29', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(dt_k2_relset_1, axiom,
% 0.49/0.68    (![A:$i,B:$i,C:$i]:
% 0.49/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.68       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.49/0.68  thf('30', plain,
% 0.49/0.68      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.49/0.68         ((m1_subset_1 @ (k2_relset_1 @ X20 @ X21 @ X22) @ (k1_zfmisc_1 @ X21))
% 0.49/0.68          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.49/0.68  thf('31', plain,
% 0.49/0.68      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_C @ sk_D_2) @ 
% 0.49/0.68        (k1_zfmisc_1 @ sk_C))),
% 0.49/0.68      inference('sup-', [status(thm)], ['29', '30'])).
% 0.49/0.68  thf('32', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(redefinition_k2_relset_1, axiom,
% 0.49/0.68    (![A:$i,B:$i,C:$i]:
% 0.49/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.68       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.49/0.68  thf('33', plain,
% 0.49/0.68      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.49/0.68         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.49/0.68          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.49/0.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.49/0.68  thf('34', plain,
% 0.49/0.68      (((k2_relset_1 @ sk_A @ sk_C @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.49/0.68      inference('sup-', [status(thm)], ['32', '33'])).
% 0.49/0.68  thf('35', plain,
% 0.49/0.68      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ (k1_zfmisc_1 @ sk_C))),
% 0.49/0.68      inference('demod', [status(thm)], ['31', '34'])).
% 0.49/0.68  thf(l3_subset_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.49/0.68  thf('36', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.68         (~ (r2_hidden @ X0 @ X1)
% 0.49/0.68          | (r2_hidden @ X0 @ X2)
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.49/0.68      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.49/0.68  thf('37', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((r2_hidden @ X0 @ sk_C) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.49/0.68  thf('38', plain,
% 0.49/0.68      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C))
% 0.49/0.68         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['28', '37'])).
% 0.49/0.68  thf(t1_subset, axiom,
% 0.49/0.68    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.49/0.68  thf('39', plain,
% 0.49/0.68      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.49/0.68      inference('cnf', [status(esa)], [t1_subset])).
% 0.49/0.68  thf('40', plain,
% 0.49/0.68      (((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C))
% 0.49/0.68         <= (((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['38', '39'])).
% 0.49/0.68  thf('41', plain,
% 0.49/0.68      (~ ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))) | 
% 0.49/0.68       ~
% 0.49/0.68       (![X30 : $i]:
% 0.49/0.68          (~ (m1_subset_1 @ X30 @ sk_C)
% 0.49/0.68           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X30) @ sk_D_2)
% 0.49/0.68           | ~ (r2_hidden @ X30 @ sk_B)))),
% 0.49/0.68      inference('demod', [status(thm)], ['18', '23', '40'])).
% 0.49/0.68  thf('42', plain,
% 0.49/0.68      (((m1_subset_1 @ sk_F @ sk_C)) <= (((m1_subset_1 @ sk_F @ sk_C)))),
% 0.49/0.68      inference('split', [status(esa)], ['2'])).
% 0.49/0.68  thf('43', plain,
% 0.49/0.68      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.49/0.68      inference('split', [status(esa)], ['7'])).
% 0.49/0.68  thf('44', plain,
% 0.49/0.68      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2))
% 0.49/0.68         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.49/0.68      inference('split', [status(esa)], ['0'])).
% 0.49/0.68  thf('45', plain,
% 0.49/0.68      ((![X30 : $i]:
% 0.49/0.68          (~ (m1_subset_1 @ X30 @ sk_C)
% 0.49/0.68           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X30) @ sk_D_2)
% 0.49/0.68           | ~ (r2_hidden @ X30 @ sk_B)))
% 0.49/0.68         <= ((![X30 : $i]:
% 0.49/0.68                (~ (m1_subset_1 @ X30 @ sk_C)
% 0.49/0.68                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X30) @ sk_D_2)
% 0.49/0.68                 | ~ (r2_hidden @ X30 @ sk_B))))),
% 0.49/0.68      inference('split', [status(esa)], ['16'])).
% 0.49/0.68  thf('46', plain,
% 0.49/0.68      (((~ (r2_hidden @ sk_F @ sk_B) | ~ (m1_subset_1 @ sk_F @ sk_C)))
% 0.49/0.68         <= ((![X30 : $i]:
% 0.49/0.68                (~ (m1_subset_1 @ X30 @ sk_C)
% 0.49/0.68                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X30) @ sk_D_2)
% 0.49/0.68                 | ~ (r2_hidden @ X30 @ sk_B))) & 
% 0.49/0.68             ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['44', '45'])).
% 0.49/0.68  thf('47', plain,
% 0.49/0.68      ((~ (m1_subset_1 @ sk_F @ sk_C))
% 0.49/0.68         <= ((![X30 : $i]:
% 0.49/0.68                (~ (m1_subset_1 @ X30 @ sk_C)
% 0.49/0.68                 | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X30) @ sk_D_2)
% 0.49/0.68                 | ~ (r2_hidden @ X30 @ sk_B))) & 
% 0.49/0.68             ((r2_hidden @ sk_F @ sk_B)) & 
% 0.49/0.68             ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['43', '46'])).
% 0.49/0.68  thf('48', plain,
% 0.49/0.68      (~ ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)) | 
% 0.49/0.68       ~
% 0.49/0.68       (![X30 : $i]:
% 0.49/0.68          (~ (m1_subset_1 @ X30 @ sk_C)
% 0.49/0.68           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X30) @ sk_D_2)
% 0.49/0.68           | ~ (r2_hidden @ X30 @ sk_B))) | 
% 0.49/0.68       ~ ((m1_subset_1 @ sk_F @ sk_C)) | ~ ((r2_hidden @ sk_F @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['42', '47'])).
% 0.49/0.68  thf('49', plain,
% 0.49/0.68      (~ ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))) | 
% 0.49/0.68       (![X30 : $i]:
% 0.49/0.68          (~ (m1_subset_1 @ X30 @ sk_C)
% 0.49/0.68           | ~ (r2_hidden @ (k4_tarski @ sk_E_2 @ X30) @ sk_D_2)
% 0.49/0.68           | ~ (r2_hidden @ X30 @ sk_B)))),
% 0.49/0.68      inference('split', [status(esa)], ['16'])).
% 0.49/0.68  thf('50', plain,
% 0.49/0.68      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.49/0.68       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.49/0.68      inference('split', [status(esa)], ['7'])).
% 0.49/0.68  thf('51', plain,
% 0.49/0.68      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.49/0.68      inference('split', [status(esa)], ['7'])).
% 0.49/0.68  thf('52', plain,
% 0.49/0.68      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2))
% 0.49/0.68         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.49/0.68      inference('split', [status(esa)], ['0'])).
% 0.49/0.68  thf(d14_relat_1, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( v1_relat_1 @ A ) =>
% 0.49/0.68       ( ![B:$i,C:$i]:
% 0.49/0.68         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.49/0.68           ( ![D:$i]:
% 0.49/0.68             ( ( r2_hidden @ D @ C ) <=>
% 0.49/0.68               ( ?[E:$i]:
% 0.49/0.68                 ( ( r2_hidden @ E @ B ) & 
% 0.49/0.68                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.49/0.68  thf('53', plain,
% 0.49/0.68      (![X6 : $i, X7 : $i, X9 : $i, X11 : $i, X12 : $i]:
% 0.49/0.68         (((X9) != (k10_relat_1 @ X7 @ X6))
% 0.49/0.68          | (r2_hidden @ X11 @ X9)
% 0.49/0.69          | ~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X7)
% 0.49/0.69          | ~ (r2_hidden @ X12 @ X6)
% 0.49/0.69          | ~ (v1_relat_1 @ X7))),
% 0.49/0.69      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.49/0.69  thf('54', plain,
% 0.49/0.69      (![X6 : $i, X7 : $i, X11 : $i, X12 : $i]:
% 0.49/0.69         (~ (v1_relat_1 @ X7)
% 0.49/0.69          | ~ (r2_hidden @ X12 @ X6)
% 0.49/0.69          | ~ (r2_hidden @ (k4_tarski @ X11 @ X12) @ X7)
% 0.49/0.69          | (r2_hidden @ X11 @ (k10_relat_1 @ X7 @ X6)))),
% 0.49/0.69      inference('simplify', [status(thm)], ['53'])).
% 0.49/0.69  thf('55', plain,
% 0.49/0.69      ((![X0 : $i]:
% 0.49/0.69          ((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ X0))
% 0.49/0.69           | ~ (r2_hidden @ sk_F @ X0)
% 0.49/0.69           | ~ (v1_relat_1 @ sk_D_2)))
% 0.49/0.69         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['52', '54'])).
% 0.49/0.69  thf('56', plain, ((v1_relat_1 @ sk_D_2)),
% 0.49/0.69      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.69  thf('57', plain,
% 0.49/0.69      ((![X0 : $i]:
% 0.49/0.69          ((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ X0))
% 0.49/0.69           | ~ (r2_hidden @ sk_F @ X0)))
% 0.49/0.69         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.49/0.69      inference('demod', [status(thm)], ['55', '56'])).
% 0.49/0.69  thf('58', plain,
% 0.49/0.69      (((r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.49/0.69         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.49/0.69             ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['51', '57'])).
% 0.49/0.69  thf('59', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ X0)
% 0.49/0.69           = (k10_relat_1 @ sk_D_2 @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['4', '5'])).
% 0.49/0.69  thf('60', plain,
% 0.49/0.69      ((~ (r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))
% 0.49/0.69         <= (~
% 0.49/0.69             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.49/0.69      inference('split', [status(esa)], ['16'])).
% 0.49/0.69  thf('61', plain,
% 0.49/0.69      ((~ (r2_hidden @ sk_E_2 @ (k10_relat_1 @ sk_D_2 @ sk_B)))
% 0.49/0.69         <= (~
% 0.49/0.69             ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B))))),
% 0.49/0.69      inference('sup-', [status(thm)], ['59', '60'])).
% 0.49/0.69  thf('62', plain,
% 0.49/0.69      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 0.49/0.69       ~ ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_F) @ sk_D_2)) | 
% 0.49/0.69       ((r2_hidden @ sk_E_2 @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_2 @ sk_B)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['58', '61'])).
% 0.49/0.69  thf('63', plain, ($false),
% 0.49/0.69      inference('sat_resolution*', [status(thm)],
% 0.49/0.69                ['1', '3', '41', '48', '49', '50', '62'])).
% 0.49/0.69  
% 0.49/0.69  % SZS output end Refutation
% 0.49/0.69  
% 0.49/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
