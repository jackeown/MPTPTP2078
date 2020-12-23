%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rHYT20vTZE

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:58 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 152 expanded)
%              Number of leaves         :   35 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  880 (2821 expanded)
%              Number of equality atoms :   51 ( 126 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t185_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                   => ( ( B = k1_xboole_0 )
                      | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                        = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( v1_xboole_0 @ C )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ! [E: $i] :
                ( ( ( v1_funct_1 @ E )
                  & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
               => ! [F: $i] :
                    ( ( m1_subset_1 @ F @ B )
                   => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                     => ( ( B = k1_xboole_0 )
                        | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                          = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t185_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_relat_1 @ E )
            & ( v1_funct_1 @ E ) )
         => ( ( r2_hidden @ C @ A )
           => ( ( B = k1_xboole_0 )
              | ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C )
                = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ~ ( v1_funct_1 @ X29 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X30 @ X29 ) @ X31 )
        = ( k1_funct_1 @ X29 @ ( k1_funct_1 @ X30 @ X31 ) ) )
      | ( X32 = k1_xboole_0 )
      | ~ ( r2_hidden @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ sk_F )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
      | ( sk_C_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) )
           => ( ( B = k1_xboole_0 )
              | ( ( k8_funct_2 @ A @ B @ C @ D @ E )
                = ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k8_funct_2 @ X21 @ X19 @ X20 @ X22 @ X18 )
        = ( k1_partfun1 @ X21 @ X19 @ X19 @ X20 @ X22 @ X18 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X21 @ X19 @ X22 ) @ ( k1_relset_1 @ X19 @ X20 @ X18 ) )
      | ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X19 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d12_funct_2])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C_1 @ X0 ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C_1 @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C_1 @ sk_C_1 @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C_1 @ X0 ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C_1 @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C_1 @ sk_C_1 @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','26','27','28','29'])).

thf('31',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('40',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('43',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['51','56'])).

thf('58',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['39','57'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['0','58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rHYT20vTZE
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:08:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.62  % Solved by: fo/fo7.sh
% 0.35/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.62  % done 134 iterations in 0.159s
% 0.35/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.62  % SZS output start Refutation
% 0.35/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.62  thf(sk_F_type, type, sk_F: $i).
% 0.35/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.62  thf(sk_E_type, type, sk_E: $i).
% 0.35/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.62  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.35/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.35/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.35/0.62  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.35/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.35/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.35/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.62  thf(t185_funct_2, conjecture,
% 0.35/0.62    (![A:$i,B:$i,C:$i]:
% 0.35/0.62     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.35/0.62       ( ![D:$i]:
% 0.35/0.62         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.35/0.62             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.35/0.62           ( ![E:$i]:
% 0.35/0.62             ( ( ( v1_funct_1 @ E ) & 
% 0.35/0.62                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.35/0.62               ( ![F:$i]:
% 0.35/0.62                 ( ( m1_subset_1 @ F @ B ) =>
% 0.35/0.62                   ( ( r1_tarski @
% 0.35/0.62                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.35/0.62                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.35/0.62                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.35/0.62                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.35/0.62                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.62        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.35/0.62          ( ![D:$i]:
% 0.35/0.62            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.35/0.62                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.35/0.62              ( ![E:$i]:
% 0.35/0.62                ( ( ( v1_funct_1 @ E ) & 
% 0.35/0.62                    ( m1_subset_1 @
% 0.35/0.62                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.35/0.62                  ( ![F:$i]:
% 0.35/0.62                    ( ( m1_subset_1 @ F @ B ) =>
% 0.35/0.62                      ( ( r1_tarski @
% 0.35/0.62                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.35/0.62                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.35/0.62                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.35/0.62                          ( ( k1_funct_1 @
% 0.35/0.62                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.35/0.62                            ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.35/0.62    inference('cnf.neg', [status(esa)], [t185_funct_2])).
% 0.35/0.62  thf('0', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf(t2_subset, axiom,
% 0.35/0.62    (![A:$i,B:$i]:
% 0.35/0.62     ( ( m1_subset_1 @ A @ B ) =>
% 0.35/0.62       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.35/0.62  thf('2', plain,
% 0.35/0.62      (![X11 : $i, X12 : $i]:
% 0.35/0.62         ((r2_hidden @ X11 @ X12)
% 0.35/0.62          | (v1_xboole_0 @ X12)
% 0.35/0.62          | ~ (m1_subset_1 @ X11 @ X12))),
% 0.35/0.62      inference('cnf', [status(esa)], [t2_subset])).
% 0.35/0.62  thf('3', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 0.35/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.62  thf('4', plain,
% 0.35/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf(t21_funct_2, axiom,
% 0.35/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.35/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.62       ( ![E:$i]:
% 0.35/0.62         ( ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) ) =>
% 0.35/0.62           ( ( r2_hidden @ C @ A ) =>
% 0.35/0.62             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.35/0.62               ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C ) =
% 0.35/0.62                 ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) ))).
% 0.35/0.62  thf('5', plain,
% 0.35/0.62      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.35/0.62         (~ (v1_relat_1 @ X29)
% 0.35/0.62          | ~ (v1_funct_1 @ X29)
% 0.35/0.62          | ((k1_funct_1 @ (k5_relat_1 @ X30 @ X29) @ X31)
% 0.35/0.62              = (k1_funct_1 @ X29 @ (k1_funct_1 @ X30 @ X31)))
% 0.35/0.62          | ((X32) = (k1_xboole_0))
% 0.35/0.62          | ~ (r2_hidden @ X31 @ X33)
% 0.35/0.62          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.35/0.62          | ~ (v1_funct_2 @ X30 @ X33 @ X32)
% 0.35/0.62          | ~ (v1_funct_1 @ X30))),
% 0.35/0.62      inference('cnf', [status(esa)], [t21_funct_2])).
% 0.35/0.62  thf('6', plain,
% 0.35/0.62      (![X0 : $i, X1 : $i]:
% 0.35/0.62         (~ (v1_funct_1 @ sk_D)
% 0.35/0.62          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 0.35/0.62          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.35/0.62          | ((sk_C_1) = (k1_xboole_0))
% 0.35/0.62          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.35/0.62              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.35/0.62          | ~ (v1_funct_1 @ X1)
% 0.35/0.62          | ~ (v1_relat_1 @ X1))),
% 0.35/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.35/0.62  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('8', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('9', plain,
% 0.35/0.62      (![X0 : $i, X1 : $i]:
% 0.35/0.62         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.35/0.62          | ((sk_C_1) = (k1_xboole_0))
% 0.35/0.62          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.35/0.62              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.35/0.62          | ~ (v1_funct_1 @ X1)
% 0.35/0.62          | ~ (v1_relat_1 @ X1))),
% 0.35/0.62      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.35/0.62  thf('10', plain,
% 0.35/0.62      (![X0 : $i]:
% 0.35/0.62         ((v1_xboole_0 @ sk_B_1)
% 0.35/0.62          | ~ (v1_relat_1 @ X0)
% 0.35/0.62          | ~ (v1_funct_1 @ X0)
% 0.35/0.62          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 0.35/0.62              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.35/0.62          | ((sk_C_1) = (k1_xboole_0)))),
% 0.35/0.62      inference('sup-', [status(thm)], ['3', '9'])).
% 0.35/0.62  thf('11', plain,
% 0.35/0.62      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.35/0.62        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('12', plain,
% 0.35/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf(d12_funct_2, axiom,
% 0.35/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.35/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.62       ( ![E:$i]:
% 0.35/0.62         ( ( ( v1_funct_1 @ E ) & 
% 0.35/0.62             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.35/0.62           ( ( r1_tarski @
% 0.35/0.62               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 0.35/0.62             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.35/0.62               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 0.35/0.62                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 0.35/0.62  thf('13', plain,
% 0.35/0.62      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.35/0.62         (~ (v1_funct_1 @ X18)
% 0.35/0.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.35/0.62          | ((k8_funct_2 @ X21 @ X19 @ X20 @ X22 @ X18)
% 0.35/0.62              = (k1_partfun1 @ X21 @ X19 @ X19 @ X20 @ X22 @ X18))
% 0.35/0.62          | ~ (r1_tarski @ (k2_relset_1 @ X21 @ X19 @ X22) @ 
% 0.35/0.62               (k1_relset_1 @ X19 @ X20 @ X18))
% 0.35/0.62          | ((X19) = (k1_xboole_0))
% 0.35/0.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 0.35/0.62          | ~ (v1_funct_2 @ X22 @ X21 @ X19)
% 0.35/0.62          | ~ (v1_funct_1 @ X22))),
% 0.35/0.62      inference('cnf', [status(esa)], [d12_funct_2])).
% 0.35/0.62  thf('14', plain,
% 0.35/0.62      (![X0 : $i, X1 : $i]:
% 0.35/0.62         (~ (v1_funct_1 @ X0)
% 0.35/0.62          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C_1)
% 0.35/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C_1)))
% 0.35/0.62          | ((sk_C_1) = (k1_xboole_0))
% 0.35/0.62          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C_1 @ X0) @ 
% 0.35/0.62               (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))
% 0.35/0.62          | ((k8_funct_2 @ X1 @ sk_C_1 @ sk_A @ X0 @ sk_E)
% 0.35/0.62              = (k1_partfun1 @ X1 @ sk_C_1 @ sk_C_1 @ sk_A @ X0 @ sk_E))
% 0.35/0.62          | ~ (v1_funct_1 @ sk_E))),
% 0.35/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.62  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('16', plain,
% 0.35/0.62      (![X0 : $i, X1 : $i]:
% 0.35/0.62         (~ (v1_funct_1 @ X0)
% 0.35/0.62          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C_1)
% 0.35/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C_1)))
% 0.35/0.62          | ((sk_C_1) = (k1_xboole_0))
% 0.35/0.62          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C_1 @ X0) @ 
% 0.35/0.62               (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))
% 0.35/0.62          | ((k8_funct_2 @ X1 @ sk_C_1 @ sk_A @ X0 @ sk_E)
% 0.35/0.62              = (k1_partfun1 @ X1 @ sk_C_1 @ sk_C_1 @ sk_A @ X0 @ sk_E)))),
% 0.35/0.62      inference('demod', [status(thm)], ['14', '15'])).
% 0.35/0.62  thf('17', plain,
% 0.35/0.62      ((((k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 0.35/0.62          = (k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E))
% 0.35/0.62        | ((sk_C_1) = (k1_xboole_0))
% 0.35/0.62        | ~ (m1_subset_1 @ sk_D @ 
% 0.35/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))
% 0.35/0.62        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 0.35/0.62        | ~ (v1_funct_1 @ sk_D))),
% 0.35/0.62      inference('sup-', [status(thm)], ['11', '16'])).
% 0.35/0.62  thf('18', plain,
% 0.35/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('19', plain,
% 0.35/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf(redefinition_k1_partfun1, axiom,
% 0.35/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.35/0.62     ( ( ( v1_funct_1 @ E ) & 
% 0.35/0.62         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.35/0.62         ( v1_funct_1 @ F ) & 
% 0.35/0.62         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.35/0.62       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.35/0.62  thf('20', plain,
% 0.35/0.62      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.35/0.62         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.35/0.62          | ~ (v1_funct_1 @ X23)
% 0.35/0.62          | ~ (v1_funct_1 @ X26)
% 0.35/0.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.35/0.62          | ((k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 0.35/0.62              = (k5_relat_1 @ X23 @ X26)))),
% 0.35/0.62      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.35/0.62  thf('21', plain,
% 0.35/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.62         (((k1_partfun1 @ sk_B_1 @ sk_C_1 @ X2 @ X1 @ sk_D @ X0)
% 0.35/0.62            = (k5_relat_1 @ sk_D @ X0))
% 0.35/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.35/0.62          | ~ (v1_funct_1 @ X0)
% 0.35/0.62          | ~ (v1_funct_1 @ sk_D))),
% 0.35/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.62  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('23', plain,
% 0.35/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.62         (((k1_partfun1 @ sk_B_1 @ sk_C_1 @ X2 @ X1 @ sk_D @ X0)
% 0.35/0.62            = (k5_relat_1 @ sk_D @ X0))
% 0.35/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.35/0.62          | ~ (v1_funct_1 @ X0))),
% 0.35/0.62      inference('demod', [status(thm)], ['21', '22'])).
% 0.35/0.62  thf('24', plain,
% 0.35/0.62      ((~ (v1_funct_1 @ sk_E)
% 0.35/0.62        | ((k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 0.35/0.62            = (k5_relat_1 @ sk_D @ sk_E)))),
% 0.35/0.62      inference('sup-', [status(thm)], ['18', '23'])).
% 0.35/0.62  thf('25', plain, ((v1_funct_1 @ sk_E)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('26', plain,
% 0.35/0.62      (((k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 0.35/0.62         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.35/0.62      inference('demod', [status(thm)], ['24', '25'])).
% 0.35/0.62  thf('27', plain,
% 0.35/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('28', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('29', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('30', plain,
% 0.35/0.62      ((((k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 0.35/0.62          = (k5_relat_1 @ sk_D @ sk_E))
% 0.35/0.62        | ((sk_C_1) = (k1_xboole_0)))),
% 0.35/0.62      inference('demod', [status(thm)], ['17', '26', '27', '28', '29'])).
% 0.35/0.62  thf('31', plain,
% 0.35/0.62      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.35/0.62         sk_F) != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('32', plain,
% 0.35/0.62      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.35/0.62          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.35/0.62        | ((sk_C_1) = (k1_xboole_0)))),
% 0.35/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.35/0.62  thf('33', plain,
% 0.35/0.62      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.35/0.62          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.35/0.62        | ((sk_C_1) = (k1_xboole_0))
% 0.35/0.62        | ~ (v1_funct_1 @ sk_E)
% 0.35/0.62        | ~ (v1_relat_1 @ sk_E)
% 0.35/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.35/0.62        | ((sk_C_1) = (k1_xboole_0)))),
% 0.35/0.62      inference('sup-', [status(thm)], ['10', '32'])).
% 0.35/0.62  thf('34', plain, ((v1_funct_1 @ sk_E)),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('35', plain,
% 0.35/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf(cc1_relset_1, axiom,
% 0.35/0.62    (![A:$i,B:$i,C:$i]:
% 0.35/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.62       ( v1_relat_1 @ C ) ))).
% 0.35/0.62  thf('36', plain,
% 0.35/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.62         ((v1_relat_1 @ X15)
% 0.35/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.35/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.62  thf('37', plain, ((v1_relat_1 @ sk_E)),
% 0.35/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.35/0.62  thf('38', plain,
% 0.35/0.62      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.35/0.62          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.35/0.62        | ((sk_C_1) = (k1_xboole_0))
% 0.35/0.62        | (v1_xboole_0 @ sk_B_1)
% 0.35/0.62        | ((sk_C_1) = (k1_xboole_0)))),
% 0.35/0.62      inference('demod', [status(thm)], ['33', '34', '37'])).
% 0.35/0.62  thf('39', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_C_1) = (k1_xboole_0)))),
% 0.35/0.62      inference('simplify', [status(thm)], ['38'])).
% 0.35/0.62  thf(d3_tarski, axiom,
% 0.35/0.62    (![A:$i,B:$i]:
% 0.35/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.35/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.35/0.62  thf('40', plain,
% 0.35/0.62      (![X4 : $i, X6 : $i]:
% 0.35/0.62         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.35/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.62  thf(d1_xboole_0, axiom,
% 0.35/0.62    (![A:$i]:
% 0.35/0.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.35/0.62  thf('41', plain,
% 0.35/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.35/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.35/0.62  thf('42', plain,
% 0.35/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.35/0.62      inference('sup-', [status(thm)], ['40', '41'])).
% 0.35/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.35/0.62  thf('43', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.35/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.62  thf(d10_xboole_0, axiom,
% 0.35/0.62    (![A:$i,B:$i]:
% 0.35/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.62  thf('44', plain,
% 0.35/0.62      (![X7 : $i, X9 : $i]:
% 0.35/0.62         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.35/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.62  thf('45', plain,
% 0.35/0.62      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.35/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.35/0.62  thf('46', plain,
% 0.35/0.62      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.35/0.62      inference('sup-', [status(thm)], ['42', '45'])).
% 0.35/0.62  thf('47', plain,
% 0.35/0.62      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.35/0.62      inference('sup-', [status(thm)], ['42', '45'])).
% 0.35/0.62  thf('48', plain,
% 0.35/0.62      (![X0 : $i, X1 : $i]:
% 0.35/0.62         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.35/0.62      inference('sup+', [status(thm)], ['46', '47'])).
% 0.35/0.62  thf('49', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.35/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.62  thf('50', plain,
% 0.35/0.62      (![X0 : $i]:
% 0.35/0.62         (((X0) != (k1_xboole_0))
% 0.35/0.62          | ~ (v1_xboole_0 @ X0)
% 0.35/0.62          | ~ (v1_xboole_0 @ sk_B_1))),
% 0.35/0.62      inference('sup-', [status(thm)], ['48', '49'])).
% 0.35/0.63  thf('51', plain,
% 0.35/0.63      ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.35/0.63      inference('simplify', [status(thm)], ['50'])).
% 0.35/0.63  thf('52', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.35/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.63  thf('53', plain,
% 0.35/0.63      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.35/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.35/0.63  thf(t7_ordinal1, axiom,
% 0.35/0.63    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.63  thf('54', plain,
% 0.35/0.63      (![X13 : $i, X14 : $i]:
% 0.35/0.63         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 0.35/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.35/0.63  thf('55', plain,
% 0.35/0.63      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.35/0.63      inference('sup-', [status(thm)], ['53', '54'])).
% 0.35/0.63  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.63      inference('sup-', [status(thm)], ['52', '55'])).
% 0.35/0.63  thf('57', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.35/0.63      inference('simplify_reflect+', [status(thm)], ['51', '56'])).
% 0.35/0.63  thf('58', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.35/0.63      inference('clc', [status(thm)], ['39', '57'])).
% 0.35/0.63  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.63      inference('sup-', [status(thm)], ['52', '55'])).
% 0.35/0.63  thf('60', plain, ($false),
% 0.35/0.63      inference('demod', [status(thm)], ['0', '58', '59'])).
% 0.35/0.63  
% 0.35/0.63  % SZS output end Refutation
% 0.35/0.63  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
