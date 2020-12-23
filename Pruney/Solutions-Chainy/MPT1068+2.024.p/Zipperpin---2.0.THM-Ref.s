%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qs8yHpugUw

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:00 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 155 expanded)
%              Number of leaves         :   36 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :  894 (2835 expanded)
%              Number of equality atoms :   51 ( 126 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X31 @ X30 ) @ X32 )
        = ( k1_funct_1 @ X30 @ ( k1_funct_1 @ X31 @ X32 ) ) )
      | ( X33 = k1_xboole_0 )
      | ~ ( r2_hidden @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k8_funct_2 @ X22 @ X20 @ X21 @ X23 @ X19 )
        = ( k1_partfun1 @ X22 @ X20 @ X20 @ X21 @ X23 @ X19 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X22 @ X20 @ X23 ) @ ( k1_relset_1 @ X20 @ X21 @ X19 ) )
      | ( X20 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X20 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('45',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('55',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('56',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['53','58'])).

thf('60',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['41','59'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','57'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['0','60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qs8yHpugUw
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:41:03 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.34  % Number of cores: 8
% 0.21/0.34  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.41/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.57  % Solved by: fo/fo7.sh
% 0.41/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.57  % done 134 iterations in 0.116s
% 0.41/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.57  % SZS output start Refutation
% 0.41/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.41/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.41/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.57  thf(sk_F_type, type, sk_F: $i).
% 0.41/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.41/0.57  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.41/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.41/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.41/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.57  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.41/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.57  thf(t185_funct_2, conjecture,
% 0.41/0.57    (![A:$i,B:$i,C:$i]:
% 0.41/0.57     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.41/0.57       ( ![D:$i]:
% 0.41/0.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.41/0.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.41/0.57           ( ![E:$i]:
% 0.41/0.57             ( ( ( v1_funct_1 @ E ) & 
% 0.41/0.57                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.41/0.57               ( ![F:$i]:
% 0.41/0.57                 ( ( m1_subset_1 @ F @ B ) =>
% 0.41/0.57                   ( ( r1_tarski @
% 0.41/0.57                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.41/0.57                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.41/0.57                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.41/0.57                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.41/0.57                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.57        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.41/0.57          ( ![D:$i]:
% 0.41/0.57            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.41/0.57                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.41/0.57              ( ![E:$i]:
% 0.41/0.57                ( ( ( v1_funct_1 @ E ) & 
% 0.41/0.57                    ( m1_subset_1 @
% 0.41/0.57                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.41/0.57                  ( ![F:$i]:
% 0.41/0.57                    ( ( m1_subset_1 @ F @ B ) =>
% 0.41/0.57                      ( ( r1_tarski @
% 0.41/0.57                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.41/0.57                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.41/0.57                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.41/0.57                          ( ( k1_funct_1 @
% 0.41/0.57                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.41/0.57                            ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.41/0.57    inference('cnf.neg', [status(esa)], [t185_funct_2])).
% 0.41/0.57  thf('0', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(t2_subset, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( m1_subset_1 @ A @ B ) =>
% 0.41/0.57       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.41/0.57  thf('2', plain,
% 0.41/0.57      (![X11 : $i, X12 : $i]:
% 0.41/0.57         ((r2_hidden @ X11 @ X12)
% 0.41/0.57          | (v1_xboole_0 @ X12)
% 0.41/0.57          | ~ (m1_subset_1 @ X11 @ X12))),
% 0.41/0.57      inference('cnf', [status(esa)], [t2_subset])).
% 0.41/0.57  thf('3', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 0.41/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.57  thf('4', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(t21_funct_2, axiom,
% 0.41/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.57       ( ![E:$i]:
% 0.41/0.57         ( ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) ) =>
% 0.41/0.57           ( ( r2_hidden @ C @ A ) =>
% 0.41/0.57             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.41/0.57               ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C ) =
% 0.41/0.57                 ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) ))).
% 0.41/0.57  thf('5', plain,
% 0.41/0.57      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.41/0.57         (~ (v1_relat_1 @ X30)
% 0.41/0.57          | ~ (v1_funct_1 @ X30)
% 0.41/0.57          | ((k1_funct_1 @ (k5_relat_1 @ X31 @ X30) @ X32)
% 0.41/0.57              = (k1_funct_1 @ X30 @ (k1_funct_1 @ X31 @ X32)))
% 0.41/0.57          | ((X33) = (k1_xboole_0))
% 0.41/0.57          | ~ (r2_hidden @ X32 @ X34)
% 0.41/0.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.41/0.57          | ~ (v1_funct_2 @ X31 @ X34 @ X33)
% 0.41/0.57          | ~ (v1_funct_1 @ X31))),
% 0.41/0.57      inference('cnf', [status(esa)], [t21_funct_2])).
% 0.41/0.57  thf('6', plain,
% 0.41/0.57      (![X0 : $i, X1 : $i]:
% 0.41/0.57         (~ (v1_funct_1 @ sk_D)
% 0.41/0.57          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 0.41/0.57          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.41/0.57          | ((sk_C_1) = (k1_xboole_0))
% 0.41/0.57          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.41/0.57              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.41/0.57          | ~ (v1_funct_1 @ X1)
% 0.41/0.57          | ~ (v1_relat_1 @ X1))),
% 0.41/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.57  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('8', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('9', plain,
% 0.41/0.57      (![X0 : $i, X1 : $i]:
% 0.41/0.57         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.41/0.57          | ((sk_C_1) = (k1_xboole_0))
% 0.41/0.57          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.41/0.57              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.41/0.57          | ~ (v1_funct_1 @ X1)
% 0.41/0.57          | ~ (v1_relat_1 @ X1))),
% 0.41/0.57      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.41/0.57  thf('10', plain,
% 0.41/0.57      (![X0 : $i]:
% 0.41/0.57         ((v1_xboole_0 @ sk_B_1)
% 0.41/0.57          | ~ (v1_relat_1 @ X0)
% 0.41/0.57          | ~ (v1_funct_1 @ X0)
% 0.41/0.57          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 0.41/0.57              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.41/0.57          | ((sk_C_1) = (k1_xboole_0)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['3', '9'])).
% 0.41/0.57  thf('11', plain,
% 0.41/0.57      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.41/0.57        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('12', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(d12_funct_2, axiom,
% 0.41/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.57       ( ![E:$i]:
% 0.41/0.57         ( ( ( v1_funct_1 @ E ) & 
% 0.41/0.57             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.41/0.57           ( ( r1_tarski @
% 0.41/0.57               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 0.41/0.57             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.41/0.57               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 0.41/0.57                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 0.41/0.57  thf('13', plain,
% 0.41/0.57      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.57         (~ (v1_funct_1 @ X19)
% 0.41/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.41/0.57          | ((k8_funct_2 @ X22 @ X20 @ X21 @ X23 @ X19)
% 0.41/0.57              = (k1_partfun1 @ X22 @ X20 @ X20 @ X21 @ X23 @ X19))
% 0.41/0.57          | ~ (r1_tarski @ (k2_relset_1 @ X22 @ X20 @ X23) @ 
% 0.41/0.57               (k1_relset_1 @ X20 @ X21 @ X19))
% 0.41/0.57          | ((X20) = (k1_xboole_0))
% 0.41/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X20)))
% 0.41/0.57          | ~ (v1_funct_2 @ X23 @ X22 @ X20)
% 0.41/0.57          | ~ (v1_funct_1 @ X23))),
% 0.41/0.57      inference('cnf', [status(esa)], [d12_funct_2])).
% 0.41/0.57  thf('14', plain,
% 0.41/0.57      (![X0 : $i, X1 : $i]:
% 0.41/0.57         (~ (v1_funct_1 @ X0)
% 0.41/0.57          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C_1)
% 0.41/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C_1)))
% 0.41/0.57          | ((sk_C_1) = (k1_xboole_0))
% 0.41/0.57          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C_1 @ X0) @ 
% 0.41/0.57               (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))
% 0.41/0.57          | ((k8_funct_2 @ X1 @ sk_C_1 @ sk_A @ X0 @ sk_E)
% 0.41/0.57              = (k1_partfun1 @ X1 @ sk_C_1 @ sk_C_1 @ sk_A @ X0 @ sk_E))
% 0.41/0.57          | ~ (v1_funct_1 @ sk_E))),
% 0.41/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.57  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('16', plain,
% 0.41/0.57      (![X0 : $i, X1 : $i]:
% 0.41/0.57         (~ (v1_funct_1 @ X0)
% 0.41/0.57          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C_1)
% 0.41/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C_1)))
% 0.41/0.57          | ((sk_C_1) = (k1_xboole_0))
% 0.41/0.57          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C_1 @ X0) @ 
% 0.41/0.57               (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))
% 0.41/0.57          | ((k8_funct_2 @ X1 @ sk_C_1 @ sk_A @ X0 @ sk_E)
% 0.41/0.57              = (k1_partfun1 @ X1 @ sk_C_1 @ sk_C_1 @ sk_A @ X0 @ sk_E)))),
% 0.41/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.41/0.57  thf('17', plain,
% 0.41/0.57      ((((k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 0.41/0.57          = (k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E))
% 0.41/0.57        | ((sk_C_1) = (k1_xboole_0))
% 0.41/0.57        | ~ (m1_subset_1 @ sk_D @ 
% 0.41/0.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))
% 0.41/0.57        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 0.41/0.57        | ~ (v1_funct_1 @ sk_D))),
% 0.41/0.57      inference('sup-', [status(thm)], ['11', '16'])).
% 0.41/0.57  thf('18', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('19', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(redefinition_k1_partfun1, axiom,
% 0.41/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.41/0.57     ( ( ( v1_funct_1 @ E ) & 
% 0.41/0.57         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.41/0.57         ( v1_funct_1 @ F ) & 
% 0.41/0.57         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.41/0.57       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.41/0.57  thf('20', plain,
% 0.41/0.57      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.41/0.57         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.41/0.57          | ~ (v1_funct_1 @ X24)
% 0.41/0.57          | ~ (v1_funct_1 @ X27)
% 0.41/0.57          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.41/0.57          | ((k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 0.41/0.57              = (k5_relat_1 @ X24 @ X27)))),
% 0.41/0.57      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.41/0.57  thf('21', plain,
% 0.41/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.57         (((k1_partfun1 @ sk_B_1 @ sk_C_1 @ X2 @ X1 @ sk_D @ X0)
% 0.41/0.57            = (k5_relat_1 @ sk_D @ X0))
% 0.41/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.41/0.57          | ~ (v1_funct_1 @ X0)
% 0.41/0.57          | ~ (v1_funct_1 @ sk_D))),
% 0.41/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.41/0.57  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('23', plain,
% 0.41/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.57         (((k1_partfun1 @ sk_B_1 @ sk_C_1 @ X2 @ X1 @ sk_D @ X0)
% 0.41/0.57            = (k5_relat_1 @ sk_D @ X0))
% 0.41/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.41/0.57          | ~ (v1_funct_1 @ X0))),
% 0.41/0.57      inference('demod', [status(thm)], ['21', '22'])).
% 0.41/0.57  thf('24', plain,
% 0.41/0.57      ((~ (v1_funct_1 @ sk_E)
% 0.41/0.57        | ((k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 0.41/0.57            = (k5_relat_1 @ sk_D @ sk_E)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['18', '23'])).
% 0.41/0.57  thf('25', plain, ((v1_funct_1 @ sk_E)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('26', plain,
% 0.41/0.57      (((k1_partfun1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 0.41/0.57         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.41/0.57      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.57  thf('27', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('28', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('29', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('30', plain,
% 0.41/0.57      ((((k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E)
% 0.41/0.57          = (k5_relat_1 @ sk_D @ sk_E))
% 0.41/0.57        | ((sk_C_1) = (k1_xboole_0)))),
% 0.41/0.57      inference('demod', [status(thm)], ['17', '26', '27', '28', '29'])).
% 0.41/0.57  thf('31', plain,
% 0.41/0.57      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.41/0.57         sk_F) != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('32', plain,
% 0.41/0.57      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.41/0.57          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.41/0.57        | ((sk_C_1) = (k1_xboole_0)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.41/0.57  thf('33', plain,
% 0.41/0.57      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.41/0.57          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.41/0.57        | ((sk_C_1) = (k1_xboole_0))
% 0.41/0.57        | ~ (v1_funct_1 @ sk_E)
% 0.41/0.57        | ~ (v1_relat_1 @ sk_E)
% 0.41/0.57        | (v1_xboole_0 @ sk_B_1)
% 0.41/0.57        | ((sk_C_1) = (k1_xboole_0)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['10', '32'])).
% 0.41/0.57  thf('34', plain, ((v1_funct_1 @ sk_E)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('35', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(cc2_relat_1, axiom,
% 0.41/0.57    (![A:$i]:
% 0.41/0.57     ( ( v1_relat_1 @ A ) =>
% 0.41/0.57       ( ![B:$i]:
% 0.41/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.41/0.57  thf('36', plain,
% 0.41/0.57      (![X13 : $i, X14 : $i]:
% 0.41/0.57         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.41/0.57          | (v1_relat_1 @ X13)
% 0.41/0.57          | ~ (v1_relat_1 @ X14))),
% 0.41/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.41/0.57  thf('37', plain,
% 0.41/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) | (v1_relat_1 @ sk_E))),
% 0.41/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.41/0.57  thf(fc6_relat_1, axiom,
% 0.41/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.41/0.57  thf('38', plain,
% 0.41/0.57      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.41/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.41/0.57  thf('39', plain, ((v1_relat_1 @ sk_E)),
% 0.41/0.57      inference('demod', [status(thm)], ['37', '38'])).
% 0.41/0.57  thf('40', plain,
% 0.41/0.57      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.41/0.57          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.41/0.57        | ((sk_C_1) = (k1_xboole_0))
% 0.41/0.57        | (v1_xboole_0 @ sk_B_1)
% 0.41/0.57        | ((sk_C_1) = (k1_xboole_0)))),
% 0.41/0.57      inference('demod', [status(thm)], ['33', '34', '39'])).
% 0.41/0.57  thf('41', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_C_1) = (k1_xboole_0)))),
% 0.41/0.57      inference('simplify', [status(thm)], ['40'])).
% 0.41/0.57  thf(d3_tarski, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.41/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.41/0.57  thf('42', plain,
% 0.41/0.57      (![X4 : $i, X6 : $i]:
% 0.41/0.57         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.41/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.57  thf(d1_xboole_0, axiom,
% 0.41/0.57    (![A:$i]:
% 0.41/0.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.57  thf('43', plain,
% 0.41/0.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.57  thf('44', plain,
% 0.41/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.41/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.41/0.57  thf('45', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.41/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.57  thf(d10_xboole_0, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.57  thf('46', plain,
% 0.41/0.57      (![X7 : $i, X9 : $i]:
% 0.41/0.57         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.41/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.57  thf('47', plain,
% 0.41/0.57      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.41/0.57  thf('48', plain,
% 0.41/0.57      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['44', '47'])).
% 0.41/0.57  thf('49', plain,
% 0.41/0.57      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['44', '47'])).
% 0.41/0.57  thf('50', plain,
% 0.41/0.57      (![X0 : $i, X1 : $i]:
% 0.41/0.57         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.57      inference('sup+', [status(thm)], ['48', '49'])).
% 0.41/0.57  thf('51', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('52', plain,
% 0.41/0.57      (![X0 : $i]:
% 0.41/0.57         (((X0) != (k1_xboole_0))
% 0.41/0.57          | ~ (v1_xboole_0 @ X0)
% 0.41/0.57          | ~ (v1_xboole_0 @ sk_B_1))),
% 0.41/0.57      inference('sup-', [status(thm)], ['50', '51'])).
% 0.41/0.57  thf('53', plain,
% 0.41/0.57      ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.41/0.57      inference('simplify', [status(thm)], ['52'])).
% 0.41/0.57  thf('54', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.41/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.57  thf('55', plain,
% 0.41/0.57      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.41/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.57  thf(t7_ordinal1, axiom,
% 0.41/0.57    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.57  thf('56', plain,
% 0.41/0.57      (![X17 : $i, X18 : $i]:
% 0.41/0.57         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.41/0.57      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.41/0.57  thf('57', plain,
% 0.41/0.57      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['55', '56'])).
% 0.41/0.57  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.57      inference('sup-', [status(thm)], ['54', '57'])).
% 0.41/0.57  thf('59', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.41/0.57      inference('simplify_reflect+', [status(thm)], ['53', '58'])).
% 0.41/0.57  thf('60', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.41/0.57      inference('clc', [status(thm)], ['41', '59'])).
% 0.41/0.57  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.57      inference('sup-', [status(thm)], ['54', '57'])).
% 0.41/0.57  thf('62', plain, ($false),
% 0.41/0.57      inference('demod', [status(thm)], ['0', '60', '61'])).
% 0.41/0.57  
% 0.41/0.57  % SZS output end Refutation
% 0.41/0.57  
% 0.41/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
