%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9ic5Coa4mA

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 168 expanded)
%              Number of leaves         :   42 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          : 1079 (3385 expanded)
%              Number of equality atoms :   81 ( 175 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X4 @ X3 ) @ X5 )
        = ( k1_funct_1 @ X3 @ ( k1_funct_1 @ X4 @ X5 ) ) )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( sk_C = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( sk_C = o_0_0_xboole_0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ sk_F )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
      | ( sk_C = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','25'])).

thf('27',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k8_funct_2 @ X15 @ X13 @ X14 @ X16 @ X12 )
        = ( k1_partfun1 @ X15 @ X13 @ X13 @ X14 @ X16 @ X12 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X15 @ X13 @ X16 ) @ ( k1_relset_1 @ X13 @ X14 @ X12 ) )
      | ( X13 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X15 @ X13 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d12_funct_2])).

thf('34',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('35',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k8_funct_2 @ X15 @ X13 @ X14 @ X16 @ X12 )
        = ( k1_partfun1 @ X15 @ X13 @ X13 @ X14 @ X16 @ X12 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X15 @ X13 @ X16 ) @ ( k1_relset_1 @ X13 @ X14 @ X12 ) )
      | ( X13 = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X15 @ X13 )
      | ~ ( v1_funct_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('38',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C = o_0_0_xboole_0 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('43',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 )
        = ( k5_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( sk_C = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['40','49','50','51','52'])).

thf('54',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = o_0_0_xboole_0 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_C = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('60',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = o_0_0_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_C = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('63',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('64',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( sk_B = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('69',plain,(
    sk_B != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    sk_C = o_0_0_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['66','69'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('71',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['0','70','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9ic5Coa4mA
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:30:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 57 iterations in 0.037s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.50  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(t185_funct_2, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.50       ( ![D:$i]:
% 0.21/0.50         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.50             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.50           ( ![E:$i]:
% 0.21/0.50             ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.50                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.21/0.50               ( ![F:$i]:
% 0.21/0.50                 ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.50                   ( ( r1_tarski @
% 0.21/0.50                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.21/0.50                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.21/0.50                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.21/0.50                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.50        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.50          ( ![D:$i]:
% 0.21/0.50            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.21/0.50                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.50              ( ![E:$i]:
% 0.21/0.50                ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.50                    ( m1_subset_1 @
% 0.21/0.50                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.21/0.50                  ( ![F:$i]:
% 0.21/0.50                    ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.50                      ( ( r1_tarski @
% 0.21/0.50                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.21/0.50                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.21/0.50                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50                          ( ( k1_funct_1 @
% 0.21/0.50                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.21/0.50                            ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t185_funct_2])).
% 0.21/0.50  thf('0', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t2_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.50       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i]:
% 0.21/0.50         ((r2_hidden @ X1 @ X2)
% 0.21/0.50          | (v1_xboole_0 @ X2)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.50  thf('3', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf(d1_funct_2, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.50           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.50             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.50         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.50           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.50             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_1, axiom,
% 0.21/0.50    (![B:$i,A:$i]:
% 0.21/0.50     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.50       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i]:
% 0.21/0.50         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.50  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.21/0.50  thf('5', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i]:
% 0.21/0.50         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (o_0_0_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.50  thf(zf_stmt_3, axiom,
% 0.21/0.50    (![C:$i,B:$i,A:$i]:
% 0.21/0.50     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.50       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.50  thf(zf_stmt_5, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.50         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.50           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.50         (~ (zip_tseitin_0 @ X22 @ X23)
% 0.21/0.50          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 0.21/0.50          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      ((((sk_C) = (o_0_0_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_C @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.50  thf('11', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.50         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.21/0.50          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 0.21/0.50          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B)
% 0.21/0.50        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.50         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.21/0.50          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (((k1_relset_1 @ sk_B @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 0.21/0.50      inference('demod', [status(thm)], ['13', '16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      ((((sk_C) = (o_0_0_xboole_0)) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '17'])).
% 0.21/0.50  thf(t23_funct_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.50           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.50             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.21/0.50               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X3)
% 0.21/0.50          | ~ (v1_funct_1 @ X3)
% 0.21/0.50          | ((k1_funct_1 @ (k5_relat_1 @ X4 @ X3) @ X5)
% 0.21/0.50              = (k1_funct_1 @ X3 @ (k1_funct_1 @ X4 @ X5)))
% 0.21/0.50          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X4))
% 0.21/0.50          | ~ (v1_funct_1 @ X4)
% 0.21/0.50          | ~ (v1_relat_1 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.50          | ((sk_C) = (o_0_0_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ sk_D)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.50          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.21/0.50              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.21/0.50          | ~ (v1_funct_1 @ X1)
% 0.21/0.50          | ~ (v1_relat_1 @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc1_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( v1_relat_1 @ C ) ))).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.50         ((v1_relat_1 @ X6)
% 0.21/0.50          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.50  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf('24', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.50          | ((sk_C) = (o_0_0_xboole_0))
% 0.21/0.50          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 0.21/0.50              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 0.21/0.50          | ~ (v1_funct_1 @ X1)
% 0.21/0.50          | ~ (v1_relat_1 @ X1))),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '23', '24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ sk_B)
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 0.21/0.50              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.21/0.50          | ((sk_C) = (o_0_0_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '25'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.50        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.50         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.21/0.50          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.21/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.21/0.50      inference('demod', [status(thm)], ['27', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d12_funct_2, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.50       ( ![E:$i]:
% 0.21/0.50         ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.50             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.21/0.50           ( ( r1_tarski @
% 0.21/0.50               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 0.21/0.50             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 0.21/0.50                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X12)
% 0.21/0.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.21/0.50          | ((k8_funct_2 @ X15 @ X13 @ X14 @ X16 @ X12)
% 0.21/0.50              = (k1_partfun1 @ X15 @ X13 @ X13 @ X14 @ X16 @ X12))
% 0.21/0.50          | ~ (r1_tarski @ (k2_relset_1 @ X15 @ X13 @ X16) @ 
% 0.21/0.50               (k1_relset_1 @ X13 @ X14 @ X12))
% 0.21/0.50          | ((X13) = (k1_xboole_0))
% 0.21/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X13)))
% 0.21/0.50          | ~ (v1_funct_2 @ X16 @ X15 @ X13)
% 0.21/0.50          | ~ (v1_funct_1 @ X16))),
% 0.21/0.50      inference('cnf', [status(esa)], [d12_funct_2])).
% 0.21/0.50  thf('34', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X12)
% 0.21/0.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.21/0.50          | ((k8_funct_2 @ X15 @ X13 @ X14 @ X16 @ X12)
% 0.21/0.50              = (k1_partfun1 @ X15 @ X13 @ X13 @ X14 @ X16 @ X12))
% 0.21/0.50          | ~ (r1_tarski @ (k2_relset_1 @ X15 @ X13 @ X16) @ 
% 0.21/0.50               (k1_relset_1 @ X13 @ X14 @ X12))
% 0.21/0.50          | ((X13) = (o_0_0_xboole_0))
% 0.21/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X13)))
% 0.21/0.50          | ~ (v1_funct_2 @ X16 @ X15 @ X13)
% 0.21/0.50          | ~ (v1_funct_1 @ X16))),
% 0.21/0.50      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 0.21/0.50          | ((sk_C) = (o_0_0_xboole_0))
% 0.21/0.50          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 0.21/0.50               (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 0.21/0.50          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 0.21/0.50              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E))
% 0.21/0.50          | ~ (v1_funct_1 @ sk_E))),
% 0.21/0.50      inference('sup-', [status(thm)], ['32', '35'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.21/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.50  thf('38', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 0.21/0.50          | ((sk_C) = (o_0_0_xboole_0))
% 0.21/0.50          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ (k1_relat_1 @ sk_E))
% 0.21/0.50          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 0.21/0.50              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E)))),
% 0.21/0.50      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.21/0.50          = (k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E))
% 0.21/0.50        | ((sk_C) = (o_0_0_xboole_0))
% 0.21/0.50        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))
% 0.21/0.50        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['31', '39'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k1_partfun1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.50         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.50         ( v1_funct_1 @ F ) & 
% 0.21/0.50         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.21/0.50       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.21/0.50          | ~ (v1_funct_1 @ X25)
% 0.21/0.50          | ~ (v1_funct_1 @ X28)
% 0.21/0.50          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.21/0.50          | ((k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28)
% 0.21/0.50              = (k5_relat_1 @ X25 @ X28)))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 0.21/0.50            = (k5_relat_1 @ sk_D @ X0))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.50  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 0.21/0.50            = (k5_relat_1 @ sk_D @ X0))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.50          | ~ (v1_funct_1 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      ((~ (v1_funct_1 @ sk_E)
% 0.21/0.50        | ((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.21/0.50            = (k5_relat_1 @ sk_D @ sk_E)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['41', '46'])).
% 0.21/0.50  thf('48', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.21/0.50         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.21/0.50      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('51', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 0.21/0.50          = (k5_relat_1 @ sk_D @ sk_E))
% 0.21/0.50        | ((sk_C) = (o_0_0_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['40', '49', '50', '51', '52'])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.21/0.50         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.21/0.50          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.21/0.50        | ((sk_C) = (o_0_0_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.21/0.50          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.21/0.50        | ((sk_C) = (o_0_0_xboole_0))
% 0.21/0.50        | ~ (v1_funct_1 @ sk_E)
% 0.21/0.50        | ~ (v1_relat_1 @ sk_E)
% 0.21/0.50        | (v1_xboole_0 @ sk_B)
% 0.21/0.50        | ((sk_C) = (o_0_0_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['26', '55'])).
% 0.21/0.50  thf('57', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('59', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.50         ((v1_relat_1 @ X6)
% 0.21/0.50          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.50  thf('60', plain, ((v1_relat_1 @ sk_E)),
% 0.21/0.50      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 0.21/0.50          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 0.21/0.50        | ((sk_C) = (o_0_0_xboole_0))
% 0.21/0.50        | (v1_xboole_0 @ sk_B)
% 0.21/0.50        | ((sk_C) = (o_0_0_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['56', '57', '60'])).
% 0.21/0.50  thf('62', plain, (((v1_xboole_0 @ sk_B) | ((sk_C) = (o_0_0_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['61'])).
% 0.21/0.50  thf(l13_xboole_0, axiom,
% 0.21/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.50  thf('64', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.50  thf('65', plain,
% 0.21/0.50      (![X0 : $i]: (((X0) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      ((((sk_C) = (o_0_0_xboole_0)) | ((sk_B) = (o_0_0_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['62', '65'])).
% 0.21/0.50  thf('67', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('68', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.50  thf('69', plain, (((sk_B) != (o_0_0_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.50  thf('70', plain, (((sk_C) = (o_0_0_xboole_0))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['66', '69'])).
% 0.21/0.50  thf(dt_o_0_0_xboole_0, axiom, (v1_xboole_0 @ o_0_0_xboole_0)).
% 0.21/0.50  thf('71', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.21/0.50  thf('72', plain, ($false),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '70', '71'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
