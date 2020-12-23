%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.15LmWUx0v6

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:00 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 133 expanded)
%              Number of leaves         :   31 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  817 (2701 expanded)
%              Number of equality atoms :   51 ( 128 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( v1_xboole_0 @ sk_C ) ),
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
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X19 @ X18 ) @ X20 )
        = ( k1_funct_1 @ X18 @ ( k1_funct_1 @ X19 @ X20 ) ) )
      | ( X21 = k1_xboole_0 )
      | ~ ( r2_hidden @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( sk_C = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( sk_C = k1_xboole_0 )
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
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_funct_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( ( k8_funct_2 @ X10 @ X8 @ X9 @ X11 @ X7 )
        = ( k1_partfun1 @ X10 @ X8 @ X8 @ X9 @ X11 @ X7 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X10 @ X8 @ X11 ) @ ( k1_relset_1 @ X8 @ X9 @ X7 ) )
      | ( X8 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X10 @ X8 )
      | ~ ( v1_funct_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d12_funct_2])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B_1 @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( ( k1_partfun1 @ X13 @ X14 @ X16 @ X17 @ X12 @ X15 )
        = ( k5_relat_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B_1 @ sk_C @ X2 @ X1 @ sk_D @ X0 )
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
      ( ( ( k1_partfun1 @ sk_B_1 @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B_1 @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_partfun1 @ sk_B_1 @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','26','27','28','29'])).

thf('31',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X1: $i] :
      ( v1_xboole_0 @ ( sk_B @ X1 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('47',plain,(
    ! [X1: $i] :
      ( v1_xboole_0 @ ( sk_B @ X1 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['45','50'])).

thf('52',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['39','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['46','49'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.15LmWUx0v6
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.71  % Solved by: fo/fo7.sh
% 0.47/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.71  % done 229 iterations in 0.262s
% 0.47/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.71  % SZS output start Refutation
% 0.47/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.71  thf(sk_F_type, type, sk_F: $i).
% 0.47/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.71  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.47/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.71  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.71  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.47/0.71  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.71  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.47/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.71  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.47/0.71  thf(sk_E_type, type, sk_E: $i).
% 0.47/0.71  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.47/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.71  thf(t185_funct_2, conjecture,
% 0.47/0.71    (![A:$i,B:$i,C:$i]:
% 0.47/0.71     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.47/0.71       ( ![D:$i]:
% 0.47/0.71         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.47/0.71             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.47/0.71           ( ![E:$i]:
% 0.47/0.71             ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.71                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.47/0.71               ( ![F:$i]:
% 0.47/0.71                 ( ( m1_subset_1 @ F @ B ) =>
% 0.47/0.71                   ( ( r1_tarski @
% 0.47/0.71                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.47/0.71                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.47/0.71                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.47/0.71                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.47/0.71                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.71        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.47/0.71          ( ![D:$i]:
% 0.47/0.71            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.47/0.71                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.47/0.71              ( ![E:$i]:
% 0.47/0.71                ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.71                    ( m1_subset_1 @
% 0.47/0.71                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.47/0.71                  ( ![F:$i]:
% 0.47/0.71                    ( ( m1_subset_1 @ F @ B ) =>
% 0.47/0.71                      ( ( r1_tarski @
% 0.47/0.71                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.47/0.71                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.47/0.71                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.47/0.71                          ( ( k1_funct_1 @
% 0.47/0.71                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.47/0.71                            ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.47/0.71    inference('cnf.neg', [status(esa)], [t185_funct_2])).
% 0.47/0.71  thf('0', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(t2_subset, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( m1_subset_1 @ A @ B ) =>
% 0.47/0.71       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.47/0.71  thf('2', plain,
% 0.47/0.71      (![X2 : $i, X3 : $i]:
% 0.47/0.71         ((r2_hidden @ X2 @ X3)
% 0.47/0.71          | (v1_xboole_0 @ X3)
% 0.47/0.71          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.47/0.71      inference('cnf', [status(esa)], [t2_subset])).
% 0.47/0.71  thf('3', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 0.47/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.71  thf('4', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(t21_funct_2, axiom,
% 0.47/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.71       ( ![E:$i]:
% 0.47/0.71         ( ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) ) =>
% 0.47/0.71           ( ( r2_hidden @ C @ A ) =>
% 0.47/0.71             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.47/0.71               ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C ) =
% 0.47/0.71                 ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) ))).
% 0.47/0.71  thf('5', plain,
% 0.47/0.71      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.71         (~ (v1_relat_1 @ X18)
% 0.47/0.71          | ~ (v1_funct_1 @ X18)
% 0.47/0.71          | ((k1_funct_1 @ (k5_relat_1 @ X19 @ X18) @ X20)
% 0.47/0.71              = (k1_funct_1 @ X18 @ (k1_funct_1 @ X19 @ X20)))
% 0.47/0.71          | ((X21) = (k1_xboole_0))
% 0.47/0.71          | ~ (r2_hidden @ X20 @ X22)
% 0.47/0.71          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.47/0.71          | ~ (v1_funct_2 @ X19 @ X22 @ X21)
% 0.47/0.71          | ~ (v1_funct_1 @ X19))),
% 0.47/0.71      inference('cnf', [status(esa)], [t21_funct_2])).
% 0.47/0.71  thf('6', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         (~ (v1_funct_1 @ sk_D)
% 0.47/0.71          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C)
% 0.47/0.71          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.47/0.71          | ((sk_C) = (k1_xboole_0))
% 0.47/0.71          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.47/0.71              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.47/0.71          | ~ (v1_funct_1 @ X1)
% 0.47/0.71          | ~ (v1_relat_1 @ X1))),
% 0.47/0.71      inference('sup-', [status(thm)], ['4', '5'])).
% 0.47/0.71  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('8', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('9', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.47/0.71          | ((sk_C) = (k1_xboole_0))
% 0.47/0.71          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.47/0.71              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.47/0.71          | ~ (v1_funct_1 @ X1)
% 0.47/0.71          | ~ (v1_relat_1 @ X1))),
% 0.47/0.71      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.47/0.71  thf('10', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((v1_xboole_0 @ sk_B_1)
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 0.47/0.71              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.47/0.71          | ((sk_C) = (k1_xboole_0)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['3', '9'])).
% 0.47/0.71  thf('11', plain,
% 0.47/0.71      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D) @ 
% 0.47/0.71        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('12', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(d12_funct_2, axiom,
% 0.47/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.71       ( ![E:$i]:
% 0.47/0.71         ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.71             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.47/0.71           ( ( r1_tarski @
% 0.47/0.71               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 0.47/0.71             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.47/0.71               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 0.47/0.71                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 0.47/0.71  thf('13', plain,
% 0.47/0.71      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.47/0.71         (~ (v1_funct_1 @ X7)
% 0.47/0.71          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.47/0.71          | ((k8_funct_2 @ X10 @ X8 @ X9 @ X11 @ X7)
% 0.47/0.71              = (k1_partfun1 @ X10 @ X8 @ X8 @ X9 @ X11 @ X7))
% 0.47/0.71          | ~ (r1_tarski @ (k2_relset_1 @ X10 @ X8 @ X11) @ 
% 0.47/0.71               (k1_relset_1 @ X8 @ X9 @ X7))
% 0.47/0.71          | ((X8) = (k1_xboole_0))
% 0.47/0.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X8)))
% 0.47/0.71          | ~ (v1_funct_2 @ X11 @ X10 @ X8)
% 0.47/0.71          | ~ (v1_funct_1 @ X11))),
% 0.47/0.71      inference('cnf', [status(esa)], [d12_funct_2])).
% 0.47/0.71  thf('14', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         (~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 0.47/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 0.47/0.71          | ((sk_C) = (k1_xboole_0))
% 0.47/0.71          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 0.47/0.71               (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 0.47/0.71          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 0.47/0.71              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E))
% 0.47/0.71          | ~ (v1_funct_1 @ sk_E))),
% 0.47/0.71      inference('sup-', [status(thm)], ['12', '13'])).
% 0.47/0.71  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('16', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         (~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 0.47/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 0.47/0.71          | ((sk_C) = (k1_xboole_0))
% 0.47/0.71          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 0.47/0.71               (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 0.47/0.71          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 0.47/0.71              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E)))),
% 0.47/0.71      inference('demod', [status(thm)], ['14', '15'])).
% 0.47/0.71  thf('17', plain,
% 0.47/0.71      ((((k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.47/0.71          = (k1_partfun1 @ sk_B_1 @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E))
% 0.47/0.71        | ((sk_C) = (k1_xboole_0))
% 0.47/0.71        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))
% 0.47/0.71        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C)
% 0.47/0.71        | ~ (v1_funct_1 @ sk_D))),
% 0.47/0.71      inference('sup-', [status(thm)], ['11', '16'])).
% 0.47/0.71  thf('18', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('19', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(redefinition_k1_partfun1, axiom,
% 0.47/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.47/0.71     ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.71         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.47/0.71         ( v1_funct_1 @ F ) & 
% 0.47/0.71         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.47/0.71       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.47/0.71  thf('20', plain,
% 0.47/0.71      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.47/0.71         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.47/0.71          | ~ (v1_funct_1 @ X12)
% 0.47/0.71          | ~ (v1_funct_1 @ X15)
% 0.47/0.71          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.47/0.71          | ((k1_partfun1 @ X13 @ X14 @ X16 @ X17 @ X12 @ X15)
% 0.47/0.71              = (k5_relat_1 @ X12 @ X15)))),
% 0.47/0.71      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.47/0.71  thf('21', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.71         (((k1_partfun1 @ sk_B_1 @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 0.47/0.71            = (k5_relat_1 @ sk_D @ X0))
% 0.47/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ sk_D))),
% 0.47/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.71  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('23', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.71         (((k1_partfun1 @ sk_B_1 @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 0.47/0.71            = (k5_relat_1 @ sk_D @ X0))
% 0.47/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.47/0.71          | ~ (v1_funct_1 @ X0))),
% 0.47/0.71      inference('demod', [status(thm)], ['21', '22'])).
% 0.47/0.71  thf('24', plain,
% 0.47/0.71      ((~ (v1_funct_1 @ sk_E)
% 0.47/0.71        | ((k1_partfun1 @ sk_B_1 @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.47/0.71            = (k5_relat_1 @ sk_D @ sk_E)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['18', '23'])).
% 0.47/0.71  thf('25', plain, ((v1_funct_1 @ sk_E)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('26', plain,
% 0.47/0.71      (((k1_partfun1 @ sk_B_1 @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.47/0.71         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.47/0.71      inference('demod', [status(thm)], ['24', '25'])).
% 0.47/0.71  thf('27', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('28', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('29', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('30', plain,
% 0.47/0.71      ((((k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.47/0.71          = (k5_relat_1 @ sk_D @ sk_E))
% 0.47/0.71        | ((sk_C) = (k1_xboole_0)))),
% 0.47/0.71      inference('demod', [status(thm)], ['17', '26', '27', '28', '29'])).
% 0.47/0.71  thf('31', plain,
% 0.47/0.71      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.47/0.71         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('32', plain,
% 0.47/0.71      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.47/0.71          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.47/0.71        | ((sk_C) = (k1_xboole_0)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.71  thf('33', plain,
% 0.47/0.71      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.47/0.71          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.47/0.71        | ((sk_C) = (k1_xboole_0))
% 0.47/0.71        | ~ (v1_funct_1 @ sk_E)
% 0.47/0.71        | ~ (v1_relat_1 @ sk_E)
% 0.47/0.71        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.71        | ((sk_C) = (k1_xboole_0)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['10', '32'])).
% 0.47/0.71  thf('34', plain, ((v1_funct_1 @ sk_E)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('35', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(cc1_relset_1, axiom,
% 0.47/0.71    (![A:$i,B:$i,C:$i]:
% 0.47/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.71       ( v1_relat_1 @ C ) ))).
% 0.47/0.71  thf('36', plain,
% 0.47/0.71      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.47/0.71         ((v1_relat_1 @ X4)
% 0.47/0.71          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.47/0.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.71  thf('37', plain, ((v1_relat_1 @ sk_E)),
% 0.47/0.71      inference('sup-', [status(thm)], ['35', '36'])).
% 0.47/0.71  thf('38', plain,
% 0.47/0.71      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.47/0.71          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.47/0.71        | ((sk_C) = (k1_xboole_0))
% 0.47/0.71        | (v1_xboole_0 @ sk_B_1)
% 0.47/0.71        | ((sk_C) = (k1_xboole_0)))),
% 0.47/0.71      inference('demod', [status(thm)], ['33', '34', '37'])).
% 0.47/0.71  thf('39', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_C) = (k1_xboole_0)))),
% 0.47/0.71      inference('simplify', [status(thm)], ['38'])).
% 0.47/0.71  thf(l13_xboole_0, axiom,
% 0.47/0.71    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.71  thf('40', plain,
% 0.47/0.71      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.71  thf('41', plain,
% 0.47/0.71      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.71  thf('42', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.71      inference('sup+', [status(thm)], ['40', '41'])).
% 0.47/0.71  thf('43', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('44', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (((X0) != (k1_xboole_0))
% 0.47/0.71          | ~ (v1_xboole_0 @ X0)
% 0.47/0.71          | ~ (v1_xboole_0 @ sk_B_1))),
% 0.47/0.71      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.71  thf('45', plain,
% 0.47/0.71      ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.47/0.71      inference('simplify', [status(thm)], ['44'])).
% 0.47/0.71  thf(rc2_subset_1, axiom,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ?[B:$i]:
% 0.47/0.71       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.47/0.71  thf('46', plain, (![X1 : $i]: (v1_xboole_0 @ (sk_B @ X1))),
% 0.47/0.71      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.47/0.71  thf('47', plain, (![X1 : $i]: (v1_xboole_0 @ (sk_B @ X1))),
% 0.47/0.71      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.47/0.71  thf('48', plain,
% 0.47/0.71      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.71  thf('49', plain, (![X0 : $i]: ((sk_B @ X0) = (k1_xboole_0))),
% 0.47/0.71      inference('sup-', [status(thm)], ['47', '48'])).
% 0.47/0.71  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.71      inference('demod', [status(thm)], ['46', '49'])).
% 0.47/0.71  thf('51', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.47/0.71      inference('simplify_reflect+', [status(thm)], ['45', '50'])).
% 0.47/0.71  thf('52', plain, (((sk_C) = (k1_xboole_0))),
% 0.47/0.71      inference('clc', [status(thm)], ['39', '51'])).
% 0.47/0.71  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.71      inference('demod', [status(thm)], ['46', '49'])).
% 0.47/0.71  thf('54', plain, ($false),
% 0.47/0.71      inference('demod', [status(thm)], ['0', '52', '53'])).
% 0.47/0.71  
% 0.47/0.71  % SZS output end Refutation
% 0.47/0.71  
% 0.47/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
