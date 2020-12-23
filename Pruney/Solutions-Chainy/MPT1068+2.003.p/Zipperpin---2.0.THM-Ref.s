%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YfCG0BSUfP

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:57 EST 2020

% Result     : Theorem 14.03s
% Output     : Refutation 14.03s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 614 expanded)
%              Number of leaves         :   45 ( 197 expanded)
%              Depth                    :   19
%              Number of atoms          : 1251 (13746 expanded)
%              Number of equality atoms :   97 ( 703 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

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

thf('6',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ( ( sk_C = k1_xboole_0 )
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X14 @ X13 ) @ X15 )
        = ( k1_funct_1 @ X13 @ ( k1_funct_1 @ X14 @ X15 ) ) )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( sk_C = k1_xboole_0 )
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
      | ( sk_C = k1_xboole_0 )
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
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 )
        = ( k5_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
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

thf('42',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k8_funct_2 @ X28 @ X26 @ X27 @ X29 @ X25 )
        = ( k1_partfun1 @ X28 @ X26 @ X26 @ X27 @ X29 @ X25 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X28 @ X26 @ X29 ) @ ( k1_relset_1 @ X26 @ X27 @ X25 ) )
      | ( X26 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X26 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d12_funct_2])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('45',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','51'])).

thf('53',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('62',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('63',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('70',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(condensation,[status(thm)],['70'])).

thf('72',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['61','71'])).

thf('73',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['61','71'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35 != k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('78',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['61','71'])).

thf('82',plain,(
    v1_funct_2 @ sk_D @ sk_B @ k1_xboole_0 ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','82'])).

thf('84',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    sk_D = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['83','84'])).

thf('86',plain,(
    r1_tarski @ k1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','85'])).

thf('87',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('88',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k4_xboole_0 @ X4 @ X6 )
       != X4 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('91',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['86','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('95',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['61','71'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    $false ),
    inference('sup-',[status(thm)],['93','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YfCG0BSUfP
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:42:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 14.03/14.24  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 14.03/14.24  % Solved by: fo/fo7.sh
% 14.03/14.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.03/14.24  % done 18316 iterations in 13.771s
% 14.03/14.24  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 14.03/14.24  % SZS output start Refutation
% 14.03/14.24  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 14.03/14.24  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 14.03/14.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 14.03/14.24  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 14.03/14.24  thf(sk_B_type, type, sk_B: $i).
% 14.03/14.24  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 14.03/14.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 14.03/14.24  thf(sk_A_type, type, sk_A: $i).
% 14.03/14.24  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 14.03/14.24  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 14.03/14.24  thf(sk_C_type, type, sk_C: $i).
% 14.03/14.24  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 14.03/14.24  thf(sk_F_type, type, sk_F: $i).
% 14.03/14.24  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 14.03/14.24  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 14.03/14.24  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 14.03/14.24  thf(sk_E_type, type, sk_E: $i).
% 14.03/14.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 14.03/14.24  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 14.03/14.24  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 14.03/14.24  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 14.03/14.24  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 14.03/14.24  thf(sk_D_type, type, sk_D: $i).
% 14.03/14.24  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 14.03/14.24  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 14.03/14.24  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 14.03/14.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 14.03/14.24  thf(t185_funct_2, conjecture,
% 14.03/14.24    (![A:$i,B:$i,C:$i]:
% 14.03/14.24     ( ( ~( v1_xboole_0 @ C ) ) =>
% 14.03/14.24       ( ![D:$i]:
% 14.03/14.24         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 14.03/14.24             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 14.03/14.24           ( ![E:$i]:
% 14.03/14.24             ( ( ( v1_funct_1 @ E ) & 
% 14.03/14.24                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 14.03/14.24               ( ![F:$i]:
% 14.03/14.24                 ( ( m1_subset_1 @ F @ B ) =>
% 14.03/14.24                   ( ( r1_tarski @
% 14.03/14.24                       ( k2_relset_1 @ B @ C @ D ) @ 
% 14.03/14.24                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 14.03/14.24                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 14.03/14.24                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 14.03/14.24                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 14.03/14.24  thf(zf_stmt_0, negated_conjecture,
% 14.03/14.24    (~( ![A:$i,B:$i,C:$i]:
% 14.03/14.24        ( ( ~( v1_xboole_0 @ C ) ) =>
% 14.03/14.24          ( ![D:$i]:
% 14.03/14.24            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 14.03/14.24                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 14.03/14.24              ( ![E:$i]:
% 14.03/14.24                ( ( ( v1_funct_1 @ E ) & 
% 14.03/14.24                    ( m1_subset_1 @
% 14.03/14.24                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 14.03/14.24                  ( ![F:$i]:
% 14.03/14.24                    ( ( m1_subset_1 @ F @ B ) =>
% 14.03/14.24                      ( ( r1_tarski @
% 14.03/14.24                          ( k2_relset_1 @ B @ C @ D ) @ 
% 14.03/14.24                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 14.03/14.24                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 14.03/14.24                          ( ( k1_funct_1 @
% 14.03/14.24                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 14.03/14.24                            ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 14.03/14.24    inference('cnf.neg', [status(esa)], [t185_funct_2])).
% 14.03/14.24  thf('0', plain,
% 14.03/14.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf(t3_subset, axiom,
% 14.03/14.24    (![A:$i,B:$i]:
% 14.03/14.24     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 14.03/14.24  thf('1', plain,
% 14.03/14.24      (![X9 : $i, X10 : $i]:
% 14.03/14.24         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 14.03/14.24      inference('cnf', [status(esa)], [t3_subset])).
% 14.03/14.24  thf('2', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 14.03/14.24      inference('sup-', [status(thm)], ['0', '1'])).
% 14.03/14.24  thf('3', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf(t2_subset, axiom,
% 14.03/14.24    (![A:$i,B:$i]:
% 14.03/14.24     ( ( m1_subset_1 @ A @ B ) =>
% 14.03/14.24       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 14.03/14.24  thf('4', plain,
% 14.03/14.24      (![X7 : $i, X8 : $i]:
% 14.03/14.24         ((r2_hidden @ X7 @ X8)
% 14.03/14.24          | (v1_xboole_0 @ X8)
% 14.03/14.24          | ~ (m1_subset_1 @ X7 @ X8))),
% 14.03/14.24      inference('cnf', [status(esa)], [t2_subset])).
% 14.03/14.24  thf('5', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 14.03/14.24      inference('sup-', [status(thm)], ['3', '4'])).
% 14.03/14.24  thf(d1_funct_2, axiom,
% 14.03/14.24    (![A:$i,B:$i,C:$i]:
% 14.03/14.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.03/14.24       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 14.03/14.24           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 14.03/14.24             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 14.03/14.24         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 14.03/14.24           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 14.03/14.24             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 14.03/14.24  thf(zf_stmt_1, axiom,
% 14.03/14.24    (![B:$i,A:$i]:
% 14.03/14.24     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 14.03/14.24       ( zip_tseitin_0 @ B @ A ) ))).
% 14.03/14.24  thf('6', plain,
% 14.03/14.24      (![X30 : $i, X31 : $i]:
% 14.03/14.24         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_1])).
% 14.03/14.24  thf('7', plain,
% 14.03/14.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 14.03/14.24  thf(zf_stmt_3, axiom,
% 14.03/14.24    (![C:$i,B:$i,A:$i]:
% 14.03/14.24     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 14.03/14.24       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 14.03/14.24  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 14.03/14.24  thf(zf_stmt_5, axiom,
% 14.03/14.24    (![A:$i,B:$i,C:$i]:
% 14.03/14.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.03/14.24       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 14.03/14.24         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 14.03/14.24           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 14.03/14.24             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 14.03/14.24  thf('8', plain,
% 14.03/14.24      (![X35 : $i, X36 : $i, X37 : $i]:
% 14.03/14.24         (~ (zip_tseitin_0 @ X35 @ X36)
% 14.03/14.24          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 14.03/14.24          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_5])).
% 14.03/14.24  thf('9', plain,
% 14.03/14.24      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 14.03/14.24      inference('sup-', [status(thm)], ['7', '8'])).
% 14.03/14.24  thf('10', plain,
% 14.03/14.24      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_C @ sk_B))),
% 14.03/14.24      inference('sup-', [status(thm)], ['6', '9'])).
% 14.03/14.24  thf('11', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf('12', plain,
% 14.03/14.24      (![X32 : $i, X33 : $i, X34 : $i]:
% 14.03/14.24         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 14.03/14.24          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 14.03/14.24          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_3])).
% 14.03/14.24  thf('13', plain,
% 14.03/14.24      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B)
% 14.03/14.24        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 14.03/14.24      inference('sup-', [status(thm)], ['11', '12'])).
% 14.03/14.24  thf('14', plain,
% 14.03/14.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf(redefinition_k1_relset_1, axiom,
% 14.03/14.24    (![A:$i,B:$i,C:$i]:
% 14.03/14.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.03/14.24       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 14.03/14.24  thf('15', plain,
% 14.03/14.24      (![X19 : $i, X20 : $i, X21 : $i]:
% 14.03/14.24         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 14.03/14.24          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 14.03/14.24      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 14.03/14.24  thf('16', plain,
% 14.03/14.24      (((k1_relset_1 @ sk_B @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 14.03/14.24      inference('sup-', [status(thm)], ['14', '15'])).
% 14.03/14.24  thf('17', plain,
% 14.03/14.24      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 14.03/14.24      inference('demod', [status(thm)], ['13', '16'])).
% 14.03/14.24  thf('18', plain,
% 14.03/14.24      ((((sk_C) = (k1_xboole_0)) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 14.03/14.24      inference('sup-', [status(thm)], ['10', '17'])).
% 14.03/14.24  thf(t23_funct_1, axiom,
% 14.03/14.24    (![A:$i,B:$i]:
% 14.03/14.24     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 14.03/14.24       ( ![C:$i]:
% 14.03/14.24         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 14.03/14.24           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 14.03/14.24             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 14.03/14.24               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 14.03/14.24  thf('19', plain,
% 14.03/14.24      (![X13 : $i, X14 : $i, X15 : $i]:
% 14.03/14.24         (~ (v1_relat_1 @ X13)
% 14.03/14.24          | ~ (v1_funct_1 @ X13)
% 14.03/14.24          | ((k1_funct_1 @ (k5_relat_1 @ X14 @ X13) @ X15)
% 14.03/14.24              = (k1_funct_1 @ X13 @ (k1_funct_1 @ X14 @ X15)))
% 14.03/14.24          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X14))
% 14.03/14.24          | ~ (v1_funct_1 @ X14)
% 14.03/14.24          | ~ (v1_relat_1 @ X14))),
% 14.03/14.24      inference('cnf', [status(esa)], [t23_funct_1])).
% 14.03/14.24  thf('20', plain,
% 14.03/14.24      (![X0 : $i, X1 : $i]:
% 14.03/14.24         (~ (r2_hidden @ X0 @ sk_B)
% 14.03/14.24          | ((sk_C) = (k1_xboole_0))
% 14.03/14.24          | ~ (v1_relat_1 @ sk_D)
% 14.03/14.24          | ~ (v1_funct_1 @ sk_D)
% 14.03/14.24          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 14.03/14.24              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 14.03/14.24          | ~ (v1_funct_1 @ X1)
% 14.03/14.24          | ~ (v1_relat_1 @ X1))),
% 14.03/14.24      inference('sup-', [status(thm)], ['18', '19'])).
% 14.03/14.24  thf('21', plain,
% 14.03/14.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf(cc1_relset_1, axiom,
% 14.03/14.24    (![A:$i,B:$i,C:$i]:
% 14.03/14.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.03/14.24       ( v1_relat_1 @ C ) ))).
% 14.03/14.24  thf('22', plain,
% 14.03/14.24      (![X16 : $i, X17 : $i, X18 : $i]:
% 14.03/14.24         ((v1_relat_1 @ X16)
% 14.03/14.24          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 14.03/14.24      inference('cnf', [status(esa)], [cc1_relset_1])).
% 14.03/14.24  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 14.03/14.24      inference('sup-', [status(thm)], ['21', '22'])).
% 14.03/14.24  thf('24', plain, ((v1_funct_1 @ sk_D)),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf('25', plain,
% 14.03/14.24      (![X0 : $i, X1 : $i]:
% 14.03/14.24         (~ (r2_hidden @ X0 @ sk_B)
% 14.03/14.24          | ((sk_C) = (k1_xboole_0))
% 14.03/14.24          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 14.03/14.24              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 14.03/14.24          | ~ (v1_funct_1 @ X1)
% 14.03/14.24          | ~ (v1_relat_1 @ X1))),
% 14.03/14.24      inference('demod', [status(thm)], ['20', '23', '24'])).
% 14.03/14.24  thf('26', plain,
% 14.03/14.24      (![X0 : $i]:
% 14.03/14.24         ((v1_xboole_0 @ sk_B)
% 14.03/14.24          | ~ (v1_relat_1 @ X0)
% 14.03/14.24          | ~ (v1_funct_1 @ X0)
% 14.03/14.24          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 14.03/14.24              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F)))
% 14.03/14.24          | ((sk_C) = (k1_xboole_0)))),
% 14.03/14.24      inference('sup-', [status(thm)], ['5', '25'])).
% 14.03/14.24  thf('27', plain,
% 14.03/14.24      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf('28', plain,
% 14.03/14.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf(redefinition_k1_partfun1, axiom,
% 14.03/14.24    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 14.03/14.24     ( ( ( v1_funct_1 @ E ) & 
% 14.03/14.24         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 14.03/14.24         ( v1_funct_1 @ F ) & 
% 14.03/14.24         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 14.03/14.24       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 14.03/14.24  thf('29', plain,
% 14.03/14.24      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 14.03/14.24         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 14.03/14.24          | ~ (v1_funct_1 @ X38)
% 14.03/14.24          | ~ (v1_funct_1 @ X41)
% 14.03/14.24          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 14.03/14.24          | ((k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41)
% 14.03/14.24              = (k5_relat_1 @ X38 @ X41)))),
% 14.03/14.24      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 14.03/14.24  thf('30', plain,
% 14.03/14.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.03/14.24         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 14.03/14.24            = (k5_relat_1 @ sk_D @ X0))
% 14.03/14.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 14.03/14.24          | ~ (v1_funct_1 @ X0)
% 14.03/14.24          | ~ (v1_funct_1 @ sk_D))),
% 14.03/14.24      inference('sup-', [status(thm)], ['28', '29'])).
% 14.03/14.24  thf('31', plain, ((v1_funct_1 @ sk_D)),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf('32', plain,
% 14.03/14.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.03/14.24         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 14.03/14.24            = (k5_relat_1 @ sk_D @ X0))
% 14.03/14.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 14.03/14.24          | ~ (v1_funct_1 @ X0))),
% 14.03/14.24      inference('demod', [status(thm)], ['30', '31'])).
% 14.03/14.24  thf('33', plain,
% 14.03/14.24      ((~ (v1_funct_1 @ sk_E)
% 14.03/14.24        | ((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 14.03/14.24            = (k5_relat_1 @ sk_D @ sk_E)))),
% 14.03/14.24      inference('sup-', [status(thm)], ['27', '32'])).
% 14.03/14.24  thf('34', plain, ((v1_funct_1 @ sk_E)),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf('35', plain,
% 14.03/14.24      (((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 14.03/14.24         = (k5_relat_1 @ sk_D @ sk_E))),
% 14.03/14.24      inference('demod', [status(thm)], ['33', '34'])).
% 14.03/14.24  thf('36', plain,
% 14.03/14.24      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 14.03/14.24        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf('37', plain,
% 14.03/14.24      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf('38', plain,
% 14.03/14.24      (![X19 : $i, X20 : $i, X21 : $i]:
% 14.03/14.24         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 14.03/14.24          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 14.03/14.24      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 14.03/14.24  thf('39', plain,
% 14.03/14.24      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 14.03/14.24      inference('sup-', [status(thm)], ['37', '38'])).
% 14.03/14.24  thf('40', plain,
% 14.03/14.24      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 14.03/14.24      inference('demod', [status(thm)], ['36', '39'])).
% 14.03/14.24  thf('41', plain,
% 14.03/14.24      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf(d12_funct_2, axiom,
% 14.03/14.24    (![A:$i,B:$i,C:$i,D:$i]:
% 14.03/14.24     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 14.03/14.24         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 14.03/14.24       ( ![E:$i]:
% 14.03/14.24         ( ( ( v1_funct_1 @ E ) & 
% 14.03/14.24             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 14.03/14.24           ( ( r1_tarski @
% 14.03/14.24               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 14.03/14.24             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 14.03/14.24               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 14.03/14.24                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 14.03/14.24  thf('42', plain,
% 14.03/14.24      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 14.03/14.24         (~ (v1_funct_1 @ X25)
% 14.03/14.24          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 14.03/14.24          | ((k8_funct_2 @ X28 @ X26 @ X27 @ X29 @ X25)
% 14.03/14.24              = (k1_partfun1 @ X28 @ X26 @ X26 @ X27 @ X29 @ X25))
% 14.03/14.24          | ~ (r1_tarski @ (k2_relset_1 @ X28 @ X26 @ X29) @ 
% 14.03/14.24               (k1_relset_1 @ X26 @ X27 @ X25))
% 14.03/14.24          | ((X26) = (k1_xboole_0))
% 14.03/14.24          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 14.03/14.24          | ~ (v1_funct_2 @ X29 @ X28 @ X26)
% 14.03/14.24          | ~ (v1_funct_1 @ X29))),
% 14.03/14.24      inference('cnf', [status(esa)], [d12_funct_2])).
% 14.03/14.24  thf('43', plain,
% 14.03/14.24      (![X0 : $i, X1 : $i]:
% 14.03/14.24         (~ (v1_funct_1 @ X0)
% 14.03/14.24          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 14.03/14.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 14.03/14.24          | ((sk_C) = (k1_xboole_0))
% 14.03/14.24          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 14.03/14.24               (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 14.03/14.24          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 14.03/14.24              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E))
% 14.03/14.24          | ~ (v1_funct_1 @ sk_E))),
% 14.03/14.24      inference('sup-', [status(thm)], ['41', '42'])).
% 14.03/14.24  thf('44', plain,
% 14.03/14.24      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 14.03/14.24      inference('sup-', [status(thm)], ['37', '38'])).
% 14.03/14.24  thf('45', plain, ((v1_funct_1 @ sk_E)),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf('46', plain,
% 14.03/14.24      (![X0 : $i, X1 : $i]:
% 14.03/14.24         (~ (v1_funct_1 @ X0)
% 14.03/14.24          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 14.03/14.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 14.03/14.24          | ((sk_C) = (k1_xboole_0))
% 14.03/14.24          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ (k1_relat_1 @ sk_E))
% 14.03/14.24          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 14.03/14.24              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E)))),
% 14.03/14.24      inference('demod', [status(thm)], ['43', '44', '45'])).
% 14.03/14.24  thf('47', plain,
% 14.03/14.24      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 14.03/14.24          = (k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E))
% 14.03/14.24        | ((sk_C) = (k1_xboole_0))
% 14.03/14.24        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))
% 14.03/14.24        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 14.03/14.24        | ~ (v1_funct_1 @ sk_D))),
% 14.03/14.24      inference('sup-', [status(thm)], ['40', '46'])).
% 14.03/14.24  thf('48', plain,
% 14.03/14.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf('49', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf('50', plain, ((v1_funct_1 @ sk_D)),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf('51', plain,
% 14.03/14.24      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 14.03/14.24          = (k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E))
% 14.03/14.24        | ((sk_C) = (k1_xboole_0)))),
% 14.03/14.24      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 14.03/14.24  thf('52', plain,
% 14.03/14.24      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 14.03/14.24          = (k5_relat_1 @ sk_D @ sk_E))
% 14.03/14.24        | ((sk_C) = (k1_xboole_0)))),
% 14.03/14.24      inference('sup+', [status(thm)], ['35', '51'])).
% 14.03/14.24  thf('53', plain,
% 14.03/14.24      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 14.03/14.24         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf('54', plain,
% 14.03/14.24      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 14.03/14.24          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 14.03/14.24        | ((sk_C) = (k1_xboole_0)))),
% 14.03/14.24      inference('sup-', [status(thm)], ['52', '53'])).
% 14.03/14.24  thf('55', plain,
% 14.03/14.24      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 14.03/14.24          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 14.03/14.24        | ((sk_C) = (k1_xboole_0))
% 14.03/14.24        | ~ (v1_funct_1 @ sk_E)
% 14.03/14.24        | ~ (v1_relat_1 @ sk_E)
% 14.03/14.24        | (v1_xboole_0 @ sk_B)
% 14.03/14.24        | ((sk_C) = (k1_xboole_0)))),
% 14.03/14.24      inference('sup-', [status(thm)], ['26', '54'])).
% 14.03/14.24  thf('56', plain, ((v1_funct_1 @ sk_E)),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf('57', plain,
% 14.03/14.24      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf('58', plain,
% 14.03/14.24      (![X16 : $i, X17 : $i, X18 : $i]:
% 14.03/14.24         ((v1_relat_1 @ X16)
% 14.03/14.24          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 14.03/14.24      inference('cnf', [status(esa)], [cc1_relset_1])).
% 14.03/14.24  thf('59', plain, ((v1_relat_1 @ sk_E)),
% 14.03/14.24      inference('sup-', [status(thm)], ['57', '58'])).
% 14.03/14.24  thf('60', plain,
% 14.03/14.24      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 14.03/14.24          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 14.03/14.24        | ((sk_C) = (k1_xboole_0))
% 14.03/14.24        | (v1_xboole_0 @ sk_B)
% 14.03/14.24        | ((sk_C) = (k1_xboole_0)))),
% 14.03/14.24      inference('demod', [status(thm)], ['55', '56', '59'])).
% 14.03/14.24  thf('61', plain, (((v1_xboole_0 @ sk_B) | ((sk_C) = (k1_xboole_0)))),
% 14.03/14.24      inference('simplify', [status(thm)], ['60'])).
% 14.03/14.24  thf(l13_xboole_0, axiom,
% 14.03/14.24    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 14.03/14.24  thf('62', plain,
% 14.03/14.24      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 14.03/14.24      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.03/14.24  thf(t4_boole, axiom,
% 14.03/14.24    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 14.03/14.24  thf('63', plain,
% 14.03/14.24      (![X1 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 14.03/14.24      inference('cnf', [status(esa)], [t4_boole])).
% 14.03/14.24  thf('64', plain,
% 14.03/14.24      (![X0 : $i, X1 : $i]:
% 14.03/14.24         (((k4_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 14.03/14.24      inference('sup+', [status(thm)], ['62', '63'])).
% 14.03/14.24  thf('65', plain,
% 14.03/14.24      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 14.03/14.24      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.03/14.24  thf('66', plain,
% 14.03/14.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.03/14.24         (((X2) = (k4_xboole_0 @ X1 @ X0))
% 14.03/14.24          | ~ (v1_xboole_0 @ X1)
% 14.03/14.24          | ~ (v1_xboole_0 @ X2))),
% 14.03/14.24      inference('sup+', [status(thm)], ['64', '65'])).
% 14.03/14.24  thf('67', plain, (((sk_B) != (k1_xboole_0))),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf('68', plain,
% 14.03/14.24      (![X0 : $i, X1 : $i]:
% 14.03/14.24         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 14.03/14.24          | ~ (v1_xboole_0 @ sk_B)
% 14.03/14.24          | ~ (v1_xboole_0 @ X1))),
% 14.03/14.24      inference('sup-', [status(thm)], ['66', '67'])).
% 14.03/14.24  thf('69', plain,
% 14.03/14.24      (![X0 : $i, X1 : $i]:
% 14.03/14.24         (((k4_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 14.03/14.24      inference('sup+', [status(thm)], ['62', '63'])).
% 14.03/14.24  thf('70', plain,
% 14.03/14.24      (![X1 : $i]: (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ sk_B))),
% 14.03/14.24      inference('clc', [status(thm)], ['68', '69'])).
% 14.03/14.24  thf('71', plain, (~ (v1_xboole_0 @ sk_B)),
% 14.03/14.24      inference('condensation', [status(thm)], ['70'])).
% 14.03/14.24  thf('72', plain, (((sk_C) = (k1_xboole_0))),
% 14.03/14.24      inference('clc', [status(thm)], ['61', '71'])).
% 14.03/14.24  thf('73', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_B @ k1_xboole_0))),
% 14.03/14.24      inference('demod', [status(thm)], ['2', '72'])).
% 14.03/14.24  thf('74', plain,
% 14.03/14.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf('75', plain, (((sk_C) = (k1_xboole_0))),
% 14.03/14.24      inference('clc', [status(thm)], ['61', '71'])).
% 14.03/14.24  thf('76', plain,
% 14.03/14.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ k1_xboole_0)))),
% 14.03/14.24      inference('demod', [status(thm)], ['74', '75'])).
% 14.03/14.24  thf('77', plain,
% 14.03/14.24      (![X35 : $i, X36 : $i, X37 : $i]:
% 14.03/14.24         (((X35) != (k1_xboole_0))
% 14.03/14.24          | ((X36) = (k1_xboole_0))
% 14.03/14.24          | ((X37) = (k1_xboole_0))
% 14.03/14.24          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 14.03/14.24          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_5])).
% 14.03/14.24  thf('78', plain,
% 14.03/14.24      (![X36 : $i, X37 : $i]:
% 14.03/14.24         (~ (m1_subset_1 @ X37 @ 
% 14.03/14.24             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ k1_xboole_0)))
% 14.03/14.24          | ~ (v1_funct_2 @ X37 @ X36 @ k1_xboole_0)
% 14.03/14.24          | ((X37) = (k1_xboole_0))
% 14.03/14.24          | ((X36) = (k1_xboole_0)))),
% 14.03/14.24      inference('simplify', [status(thm)], ['77'])).
% 14.03/14.24  thf('79', plain,
% 14.03/14.24      ((((sk_B) = (k1_xboole_0))
% 14.03/14.24        | ((sk_D) = (k1_xboole_0))
% 14.03/14.24        | ~ (v1_funct_2 @ sk_D @ sk_B @ k1_xboole_0))),
% 14.03/14.24      inference('sup-', [status(thm)], ['76', '78'])).
% 14.03/14.24  thf('80', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf('81', plain, (((sk_C) = (k1_xboole_0))),
% 14.03/14.24      inference('clc', [status(thm)], ['61', '71'])).
% 14.03/14.24  thf('82', plain, ((v1_funct_2 @ sk_D @ sk_B @ k1_xboole_0)),
% 14.03/14.24      inference('demod', [status(thm)], ['80', '81'])).
% 14.03/14.24  thf('83', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 14.03/14.24      inference('demod', [status(thm)], ['79', '82'])).
% 14.03/14.24  thf('84', plain, (((sk_B) != (k1_xboole_0))),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf('85', plain, (((sk_D) = (k1_xboole_0))),
% 14.03/14.24      inference('simplify_reflect-', [status(thm)], ['83', '84'])).
% 14.03/14.24  thf('86', plain,
% 14.03/14.24      ((r1_tarski @ k1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ k1_xboole_0))),
% 14.03/14.24      inference('demod', [status(thm)], ['73', '85'])).
% 14.03/14.24  thf('87', plain,
% 14.03/14.24      (![X1 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 14.03/14.24      inference('cnf', [status(esa)], [t4_boole])).
% 14.03/14.24  thf(t83_xboole_1, axiom,
% 14.03/14.24    (![A:$i,B:$i]:
% 14.03/14.24     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 14.03/14.24  thf('88', plain,
% 14.03/14.24      (![X4 : $i, X6 : $i]:
% 14.03/14.24         ((r1_xboole_0 @ X4 @ X6) | ((k4_xboole_0 @ X4 @ X6) != (X4)))),
% 14.03/14.24      inference('cnf', [status(esa)], [t83_xboole_1])).
% 14.03/14.24  thf('89', plain,
% 14.03/14.24      (![X0 : $i]:
% 14.03/14.24         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 14.03/14.24      inference('sup-', [status(thm)], ['87', '88'])).
% 14.03/14.24  thf('90', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 14.03/14.24      inference('simplify', [status(thm)], ['89'])).
% 14.03/14.24  thf(t69_xboole_1, axiom,
% 14.03/14.24    (![A:$i,B:$i]:
% 14.03/14.24     ( ( ~( v1_xboole_0 @ B ) ) =>
% 14.03/14.24       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 14.03/14.24  thf('91', plain,
% 14.03/14.24      (![X2 : $i, X3 : $i]:
% 14.03/14.24         (~ (r1_xboole_0 @ X2 @ X3)
% 14.03/14.24          | ~ (r1_tarski @ X2 @ X3)
% 14.03/14.24          | (v1_xboole_0 @ X2))),
% 14.03/14.24      inference('cnf', [status(esa)], [t69_xboole_1])).
% 14.03/14.24  thf('92', plain,
% 14.03/14.24      (![X0 : $i]:
% 14.03/14.24         ((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 14.03/14.24      inference('sup-', [status(thm)], ['90', '91'])).
% 14.03/14.24  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 14.03/14.24      inference('sup-', [status(thm)], ['86', '92'])).
% 14.03/14.24  thf('94', plain,
% 14.03/14.24      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 14.03/14.24      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.03/14.24  thf('95', plain, (~ (v1_xboole_0 @ sk_C)),
% 14.03/14.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.03/14.24  thf('96', plain, (((sk_C) = (k1_xboole_0))),
% 14.03/14.24      inference('clc', [status(thm)], ['61', '71'])).
% 14.03/14.24  thf('97', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 14.03/14.24      inference('demod', [status(thm)], ['95', '96'])).
% 14.03/14.24  thf('98', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 14.03/14.24      inference('sup-', [status(thm)], ['94', '97'])).
% 14.03/14.24  thf('99', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 14.03/14.24      inference('simplify', [status(thm)], ['98'])).
% 14.03/14.24  thf('100', plain, ($false), inference('sup-', [status(thm)], ['93', '99'])).
% 14.03/14.24  
% 14.03/14.24  % SZS output end Refutation
% 14.03/14.24  
% 14.03/14.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
