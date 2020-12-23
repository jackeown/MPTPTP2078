%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i5hz0sigHE

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:57 EST 2020

% Result     : Theorem 12.74s
% Output     : Refutation 12.74s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 988 expanded)
%              Number of leaves         :   48 ( 305 expanded)
%              Depth                    :   22
%              Number of atoms          : 1280 (24265 expanded)
%              Number of equality atoms :   96 (1183 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k7_relat_1 @ X9 @ X10 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('10',plain,
    ( ( sk_D != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('12',plain,
    ( ( sk_D != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

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

thf('17',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('27',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

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

thf('30',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X13 @ X12 ) @ X14 )
        = ( k1_funct_1 @ X12 @ ( k1_funct_1 @ X13 @ X14 ) ) )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( sk_C = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( sk_C = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ sk_F )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','34'])).

thf('36',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k8_funct_2 @ X30 @ X28 @ X29 @ X31 @ X27 )
        = ( k1_partfun1 @ X30 @ X28 @ X28 @ X29 @ X31 @ X27 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X30 @ X28 @ X31 ) @ ( k1_relset_1 @ X28 @ X29 @ X27 ) )
      | ( X28 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X28 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
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
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
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

thf('50',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( ( k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43 )
        = ( k5_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','56','57','58','59'])).

thf('61',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64','67'])).

thf('69',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('70',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('71',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','73'])).

thf('75',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37 != k1_xboole_0 )
      | ( X38 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('76',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('80',plain,(
    v1_funct_2 @ sk_D @ sk_B @ k1_xboole_0 ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','80'])).

thf('82',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    sk_D = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,(
    sk_D = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('85',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','83','84'])).

thf('86',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_B ),
    inference(simplify,[status(thm)],['85'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('87',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('90',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('91',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('93',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    sk_D = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('95',plain,(
    r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_B ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('98',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    sk_C = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('100',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    $false ),
    inference('sup-',[status(thm)],['96','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i5hz0sigHE
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:56:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 12.74/12.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 12.74/12.98  % Solved by: fo/fo7.sh
% 12.74/12.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.74/12.98  % done 8020 iterations in 12.518s
% 12.74/12.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 12.74/12.98  % SZS output start Refutation
% 12.74/12.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.74/12.98  thf(sk_E_type, type, sk_E: $i).
% 12.74/12.98  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 12.74/12.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.74/12.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 12.74/12.98  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 12.74/12.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 12.74/12.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 12.74/12.98  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 12.74/12.98  thf(sk_F_type, type, sk_F: $i).
% 12.74/12.98  thf(sk_D_type, type, sk_D: $i).
% 12.74/12.98  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 12.74/12.98  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 12.74/12.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 12.74/12.98  thf(sk_C_type, type, sk_C: $i).
% 12.74/12.98  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 12.74/12.98  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 12.74/12.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 12.74/12.98  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 12.74/12.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 12.74/12.98  thf(sk_A_type, type, sk_A: $i).
% 12.74/12.98  thf(sk_B_type, type, sk_B: $i).
% 12.74/12.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.74/12.98  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 12.74/12.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 12.74/12.98  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 12.74/12.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.74/12.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 12.74/12.98  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 12.74/12.98  thf(t185_funct_2, conjecture,
% 12.74/12.98    (![A:$i,B:$i,C:$i]:
% 12.74/12.98     ( ( ~( v1_xboole_0 @ C ) ) =>
% 12.74/12.98       ( ![D:$i]:
% 12.74/12.98         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 12.74/12.98             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 12.74/12.98           ( ![E:$i]:
% 12.74/12.98             ( ( ( v1_funct_1 @ E ) & 
% 12.74/12.98                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 12.74/12.98               ( ![F:$i]:
% 12.74/12.98                 ( ( m1_subset_1 @ F @ B ) =>
% 12.74/12.98                   ( ( r1_tarski @
% 12.74/12.98                       ( k2_relset_1 @ B @ C @ D ) @ 
% 12.74/12.98                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 12.74/12.98                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 12.74/12.98                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 12.74/12.98                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 12.74/12.98  thf(zf_stmt_0, negated_conjecture,
% 12.74/12.98    (~( ![A:$i,B:$i,C:$i]:
% 12.74/12.98        ( ( ~( v1_xboole_0 @ C ) ) =>
% 12.74/12.98          ( ![D:$i]:
% 12.74/12.98            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 12.74/12.98                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 12.74/12.98              ( ![E:$i]:
% 12.74/12.98                ( ( ( v1_funct_1 @ E ) & 
% 12.74/12.98                    ( m1_subset_1 @
% 12.74/12.98                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 12.74/12.98                  ( ![F:$i]:
% 12.74/12.98                    ( ( m1_subset_1 @ F @ B ) =>
% 12.74/12.98                      ( ( r1_tarski @
% 12.74/12.98                          ( k2_relset_1 @ B @ C @ D ) @ 
% 12.74/12.98                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 12.74/12.98                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 12.74/12.98                          ( ( k1_funct_1 @
% 12.74/12.98                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 12.74/12.98                            ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 12.74/12.98    inference('cnf.neg', [status(esa)], [t185_funct_2])).
% 12.74/12.98  thf('0', plain,
% 12.74/12.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 12.74/12.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.98  thf(cc2_relset_1, axiom,
% 12.74/12.98    (![A:$i,B:$i,C:$i]:
% 12.74/12.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.74/12.98       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 12.74/12.98  thf('1', plain,
% 12.74/12.98      (![X18 : $i, X19 : $i, X20 : $i]:
% 12.74/12.98         ((v4_relat_1 @ X18 @ X19)
% 12.74/12.98          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 12.74/12.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 12.74/12.99  thf('2', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 12.74/12.99      inference('sup-', [status(thm)], ['0', '1'])).
% 12.74/12.99  thf(t209_relat_1, axiom,
% 12.74/12.99    (![A:$i,B:$i]:
% 12.74/12.99     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 12.74/12.99       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 12.74/12.99  thf('3', plain,
% 12.74/12.99      (![X7 : $i, X8 : $i]:
% 12.74/12.99         (((X7) = (k7_relat_1 @ X7 @ X8))
% 12.74/12.99          | ~ (v4_relat_1 @ X7 @ X8)
% 12.74/12.99          | ~ (v1_relat_1 @ X7))),
% 12.74/12.99      inference('cnf', [status(esa)], [t209_relat_1])).
% 12.74/12.99  thf('4', plain,
% 12.74/12.99      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_B)))),
% 12.74/12.99      inference('sup-', [status(thm)], ['2', '3'])).
% 12.74/12.99  thf('5', plain,
% 12.74/12.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf(cc1_relset_1, axiom,
% 12.74/12.99    (![A:$i,B:$i,C:$i]:
% 12.74/12.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.74/12.99       ( v1_relat_1 @ C ) ))).
% 12.74/12.99  thf('6', plain,
% 12.74/12.99      (![X15 : $i, X16 : $i, X17 : $i]:
% 12.74/12.99         ((v1_relat_1 @ X15)
% 12.74/12.99          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 12.74/12.99      inference('cnf', [status(esa)], [cc1_relset_1])).
% 12.74/12.99  thf('7', plain, ((v1_relat_1 @ sk_D)),
% 12.74/12.99      inference('sup-', [status(thm)], ['5', '6'])).
% 12.74/12.99  thf('8', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 12.74/12.99      inference('demod', [status(thm)], ['4', '7'])).
% 12.74/12.99  thf(t95_relat_1, axiom,
% 12.74/12.99    (![A:$i,B:$i]:
% 12.74/12.99     ( ( v1_relat_1 @ B ) =>
% 12.74/12.99       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 12.74/12.99         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 12.74/12.99  thf('9', plain,
% 12.74/12.99      (![X9 : $i, X10 : $i]:
% 12.74/12.99         (((k7_relat_1 @ X9 @ X10) != (k1_xboole_0))
% 12.74/12.99          | (r1_xboole_0 @ (k1_relat_1 @ X9) @ X10)
% 12.74/12.99          | ~ (v1_relat_1 @ X9))),
% 12.74/12.99      inference('cnf', [status(esa)], [t95_relat_1])).
% 12.74/12.99  thf('10', plain,
% 12.74/12.99      ((((sk_D) != (k1_xboole_0))
% 12.74/12.99        | ~ (v1_relat_1 @ sk_D)
% 12.74/12.99        | (r1_xboole_0 @ (k1_relat_1 @ sk_D) @ sk_B))),
% 12.74/12.99      inference('sup-', [status(thm)], ['8', '9'])).
% 12.74/12.99  thf('11', plain, ((v1_relat_1 @ sk_D)),
% 12.74/12.99      inference('sup-', [status(thm)], ['5', '6'])).
% 12.74/12.99  thf('12', plain,
% 12.74/12.99      ((((sk_D) != (k1_xboole_0)) | (r1_xboole_0 @ (k1_relat_1 @ sk_D) @ sk_B))),
% 12.74/12.99      inference('demod', [status(thm)], ['10', '11'])).
% 12.74/12.99  thf('13', plain,
% 12.74/12.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf('14', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf(t2_subset, axiom,
% 12.74/12.99    (![A:$i,B:$i]:
% 12.74/12.99     ( ( m1_subset_1 @ A @ B ) =>
% 12.74/12.99       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 12.74/12.99  thf('15', plain,
% 12.74/12.99      (![X3 : $i, X4 : $i]:
% 12.74/12.99         ((r2_hidden @ X3 @ X4)
% 12.74/12.99          | (v1_xboole_0 @ X4)
% 12.74/12.99          | ~ (m1_subset_1 @ X3 @ X4))),
% 12.74/12.99      inference('cnf', [status(esa)], [t2_subset])).
% 12.74/12.99  thf('16', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 12.74/12.99      inference('sup-', [status(thm)], ['14', '15'])).
% 12.74/12.99  thf(d1_funct_2, axiom,
% 12.74/12.99    (![A:$i,B:$i,C:$i]:
% 12.74/12.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.74/12.99       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 12.74/12.99           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 12.74/12.99             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 12.74/12.99         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 12.74/12.99           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 12.74/12.99             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 12.74/12.99  thf(zf_stmt_1, axiom,
% 12.74/12.99    (![B:$i,A:$i]:
% 12.74/12.99     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 12.74/12.99       ( zip_tseitin_0 @ B @ A ) ))).
% 12.74/12.99  thf('17', plain,
% 12.74/12.99      (![X32 : $i, X33 : $i]:
% 12.74/12.99         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 12.74/12.99  thf('18', plain,
% 12.74/12.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 12.74/12.99  thf(zf_stmt_3, axiom,
% 12.74/12.99    (![C:$i,B:$i,A:$i]:
% 12.74/12.99     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 12.74/12.99       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 12.74/12.99  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 12.74/12.99  thf(zf_stmt_5, axiom,
% 12.74/12.99    (![A:$i,B:$i,C:$i]:
% 12.74/12.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.74/12.99       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 12.74/12.99         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 12.74/12.99           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 12.74/12.99             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 12.74/12.99  thf('19', plain,
% 12.74/12.99      (![X37 : $i, X38 : $i, X39 : $i]:
% 12.74/12.99         (~ (zip_tseitin_0 @ X37 @ X38)
% 12.74/12.99          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 12.74/12.99          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 12.74/12.99  thf('20', plain,
% 12.74/12.99      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 12.74/12.99      inference('sup-', [status(thm)], ['18', '19'])).
% 12.74/12.99  thf('21', plain,
% 12.74/12.99      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_C @ sk_B))),
% 12.74/12.99      inference('sup-', [status(thm)], ['17', '20'])).
% 12.74/12.99  thf('22', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf('23', plain,
% 12.74/12.99      (![X34 : $i, X35 : $i, X36 : $i]:
% 12.74/12.99         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 12.74/12.99          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 12.74/12.99          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 12.74/12.99  thf('24', plain,
% 12.74/12.99      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B)
% 12.74/12.99        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 12.74/12.99      inference('sup-', [status(thm)], ['22', '23'])).
% 12.74/12.99  thf('25', plain,
% 12.74/12.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf(redefinition_k1_relset_1, axiom,
% 12.74/12.99    (![A:$i,B:$i,C:$i]:
% 12.74/12.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.74/12.99       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 12.74/12.99  thf('26', plain,
% 12.74/12.99      (![X21 : $i, X22 : $i, X23 : $i]:
% 12.74/12.99         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 12.74/12.99          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 12.74/12.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 12.74/12.99  thf('27', plain,
% 12.74/12.99      (((k1_relset_1 @ sk_B @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 12.74/12.99      inference('sup-', [status(thm)], ['25', '26'])).
% 12.74/12.99  thf('28', plain,
% 12.74/12.99      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 12.74/12.99      inference('demod', [status(thm)], ['24', '27'])).
% 12.74/12.99  thf('29', plain,
% 12.74/12.99      ((((sk_C) = (k1_xboole_0)) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 12.74/12.99      inference('sup-', [status(thm)], ['21', '28'])).
% 12.74/12.99  thf(t23_funct_1, axiom,
% 12.74/12.99    (![A:$i,B:$i]:
% 12.74/12.99     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 12.74/12.99       ( ![C:$i]:
% 12.74/12.99         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 12.74/12.99           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 12.74/12.99             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 12.74/12.99               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 12.74/12.99  thf('30', plain,
% 12.74/12.99      (![X12 : $i, X13 : $i, X14 : $i]:
% 12.74/12.99         (~ (v1_relat_1 @ X12)
% 12.74/12.99          | ~ (v1_funct_1 @ X12)
% 12.74/12.99          | ((k1_funct_1 @ (k5_relat_1 @ X13 @ X12) @ X14)
% 12.74/12.99              = (k1_funct_1 @ X12 @ (k1_funct_1 @ X13 @ X14)))
% 12.74/12.99          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X13))
% 12.74/12.99          | ~ (v1_funct_1 @ X13)
% 12.74/12.99          | ~ (v1_relat_1 @ X13))),
% 12.74/12.99      inference('cnf', [status(esa)], [t23_funct_1])).
% 12.74/12.99  thf('31', plain,
% 12.74/12.99      (![X0 : $i, X1 : $i]:
% 12.74/12.99         (~ (r2_hidden @ X0 @ sk_B)
% 12.74/12.99          | ((sk_C) = (k1_xboole_0))
% 12.74/12.99          | ~ (v1_relat_1 @ sk_D)
% 12.74/12.99          | ~ (v1_funct_1 @ sk_D)
% 12.74/12.99          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 12.74/12.99              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 12.74/12.99          | ~ (v1_funct_1 @ X1)
% 12.74/12.99          | ~ (v1_relat_1 @ X1))),
% 12.74/12.99      inference('sup-', [status(thm)], ['29', '30'])).
% 12.74/12.99  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 12.74/12.99      inference('sup-', [status(thm)], ['5', '6'])).
% 12.74/12.99  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf('34', plain,
% 12.74/12.99      (![X0 : $i, X1 : $i]:
% 12.74/12.99         (~ (r2_hidden @ X0 @ sk_B)
% 12.74/12.99          | ((sk_C) = (k1_xboole_0))
% 12.74/12.99          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 12.74/12.99              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 12.74/12.99          | ~ (v1_funct_1 @ X1)
% 12.74/12.99          | ~ (v1_relat_1 @ X1))),
% 12.74/12.99      inference('demod', [status(thm)], ['31', '32', '33'])).
% 12.74/12.99  thf('35', plain,
% 12.74/12.99      (![X0 : $i]:
% 12.74/12.99         ((v1_xboole_0 @ sk_B)
% 12.74/12.99          | ~ (v1_relat_1 @ X0)
% 12.74/12.99          | ~ (v1_funct_1 @ X0)
% 12.74/12.99          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 12.74/12.99              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F)))
% 12.74/12.99          | ((sk_C) = (k1_xboole_0)))),
% 12.74/12.99      inference('sup-', [status(thm)], ['16', '34'])).
% 12.74/12.99  thf('36', plain,
% 12.74/12.99      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 12.74/12.99        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf('37', plain,
% 12.74/12.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf('38', plain,
% 12.74/12.99      (![X21 : $i, X22 : $i, X23 : $i]:
% 12.74/12.99         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 12.74/12.99          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 12.74/12.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 12.74/12.99  thf('39', plain,
% 12.74/12.99      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 12.74/12.99      inference('sup-', [status(thm)], ['37', '38'])).
% 12.74/12.99  thf('40', plain,
% 12.74/12.99      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 12.74/12.99      inference('demod', [status(thm)], ['36', '39'])).
% 12.74/12.99  thf('41', plain,
% 12.74/12.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf(d12_funct_2, axiom,
% 12.74/12.99    (![A:$i,B:$i,C:$i,D:$i]:
% 12.74/12.99     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 12.74/12.99         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.74/12.99       ( ![E:$i]:
% 12.74/12.99         ( ( ( v1_funct_1 @ E ) & 
% 12.74/12.99             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 12.74/12.99           ( ( r1_tarski @
% 12.74/12.99               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 12.74/12.99             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 12.74/12.99               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 12.74/12.99                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 12.74/12.99  thf('42', plain,
% 12.74/12.99      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 12.74/12.99         (~ (v1_funct_1 @ X27)
% 12.74/12.99          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 12.74/12.99          | ((k8_funct_2 @ X30 @ X28 @ X29 @ X31 @ X27)
% 12.74/12.99              = (k1_partfun1 @ X30 @ X28 @ X28 @ X29 @ X31 @ X27))
% 12.74/12.99          | ~ (r1_tarski @ (k2_relset_1 @ X30 @ X28 @ X31) @ 
% 12.74/12.99               (k1_relset_1 @ X28 @ X29 @ X27))
% 12.74/12.99          | ((X28) = (k1_xboole_0))
% 12.74/12.99          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X28)))
% 12.74/12.99          | ~ (v1_funct_2 @ X31 @ X30 @ X28)
% 12.74/12.99          | ~ (v1_funct_1 @ X31))),
% 12.74/12.99      inference('cnf', [status(esa)], [d12_funct_2])).
% 12.74/12.99  thf('43', plain,
% 12.74/12.99      (![X0 : $i, X1 : $i]:
% 12.74/12.99         (~ (v1_funct_1 @ X0)
% 12.74/12.99          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 12.74/12.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 12.74/12.99          | ((sk_C) = (k1_xboole_0))
% 12.74/12.99          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 12.74/12.99               (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 12.74/12.99          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 12.74/12.99              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E))
% 12.74/12.99          | ~ (v1_funct_1 @ sk_E))),
% 12.74/12.99      inference('sup-', [status(thm)], ['41', '42'])).
% 12.74/12.99  thf('44', plain,
% 12.74/12.99      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 12.74/12.99      inference('sup-', [status(thm)], ['37', '38'])).
% 12.74/12.99  thf('45', plain, ((v1_funct_1 @ sk_E)),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf('46', plain,
% 12.74/12.99      (![X0 : $i, X1 : $i]:
% 12.74/12.99         (~ (v1_funct_1 @ X0)
% 12.74/12.99          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 12.74/12.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 12.74/12.99          | ((sk_C) = (k1_xboole_0))
% 12.74/12.99          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ (k1_relat_1 @ sk_E))
% 12.74/12.99          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 12.74/12.99              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E)))),
% 12.74/12.99      inference('demod', [status(thm)], ['43', '44', '45'])).
% 12.74/12.99  thf('47', plain,
% 12.74/12.99      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 12.74/12.99          = (k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E))
% 12.74/12.99        | ((sk_C) = (k1_xboole_0))
% 12.74/12.99        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))
% 12.74/12.99        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 12.74/12.99        | ~ (v1_funct_1 @ sk_D))),
% 12.74/12.99      inference('sup-', [status(thm)], ['40', '46'])).
% 12.74/12.99  thf('48', plain,
% 12.74/12.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf('49', plain,
% 12.74/12.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf(redefinition_k1_partfun1, axiom,
% 12.74/12.99    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 12.74/12.99     ( ( ( v1_funct_1 @ E ) & 
% 12.74/12.99         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 12.74/12.99         ( v1_funct_1 @ F ) & 
% 12.74/12.99         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 12.74/12.99       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 12.74/12.99  thf('50', plain,
% 12.74/12.99      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 12.74/12.99         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 12.74/12.99          | ~ (v1_funct_1 @ X40)
% 12.74/12.99          | ~ (v1_funct_1 @ X43)
% 12.74/12.99          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 12.74/12.99          | ((k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43)
% 12.74/12.99              = (k5_relat_1 @ X40 @ X43)))),
% 12.74/12.99      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 12.74/12.99  thf('51', plain,
% 12.74/12.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.74/12.99         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 12.74/12.99            = (k5_relat_1 @ sk_D @ X0))
% 12.74/12.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 12.74/12.99          | ~ (v1_funct_1 @ X0)
% 12.74/12.99          | ~ (v1_funct_1 @ sk_D))),
% 12.74/12.99      inference('sup-', [status(thm)], ['49', '50'])).
% 12.74/12.99  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf('53', plain,
% 12.74/12.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.74/12.99         (((k1_partfun1 @ sk_B @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 12.74/12.99            = (k5_relat_1 @ sk_D @ X0))
% 12.74/12.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 12.74/12.99          | ~ (v1_funct_1 @ X0))),
% 12.74/12.99      inference('demod', [status(thm)], ['51', '52'])).
% 12.74/12.99  thf('54', plain,
% 12.74/12.99      ((~ (v1_funct_1 @ sk_E)
% 12.74/12.99        | ((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 12.74/12.99            = (k5_relat_1 @ sk_D @ sk_E)))),
% 12.74/12.99      inference('sup-', [status(thm)], ['48', '53'])).
% 12.74/12.99  thf('55', plain, ((v1_funct_1 @ sk_E)),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf('56', plain,
% 12.74/12.99      (((k1_partfun1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 12.74/12.99         = (k5_relat_1 @ sk_D @ sk_E))),
% 12.74/12.99      inference('demod', [status(thm)], ['54', '55'])).
% 12.74/12.99  thf('57', plain,
% 12.74/12.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf('58', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf('60', plain,
% 12.74/12.99      ((((k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E)
% 12.74/12.99          = (k5_relat_1 @ sk_D @ sk_E))
% 12.74/12.99        | ((sk_C) = (k1_xboole_0)))),
% 12.74/12.99      inference('demod', [status(thm)], ['47', '56', '57', '58', '59'])).
% 12.74/12.99  thf('61', plain,
% 12.74/12.99      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 12.74/12.99         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf('62', plain,
% 12.74/12.99      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 12.74/12.99          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 12.74/12.99        | ((sk_C) = (k1_xboole_0)))),
% 12.74/12.99      inference('sup-', [status(thm)], ['60', '61'])).
% 12.74/12.99  thf('63', plain,
% 12.74/12.99      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 12.74/12.99          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 12.74/12.99        | ((sk_C) = (k1_xboole_0))
% 12.74/12.99        | ~ (v1_funct_1 @ sk_E)
% 12.74/12.99        | ~ (v1_relat_1 @ sk_E)
% 12.74/12.99        | (v1_xboole_0 @ sk_B)
% 12.74/12.99        | ((sk_C) = (k1_xboole_0)))),
% 12.74/12.99      inference('sup-', [status(thm)], ['35', '62'])).
% 12.74/12.99  thf('64', plain, ((v1_funct_1 @ sk_E)),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf('65', plain,
% 12.74/12.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf('66', plain,
% 12.74/12.99      (![X15 : $i, X16 : $i, X17 : $i]:
% 12.74/12.99         ((v1_relat_1 @ X15)
% 12.74/12.99          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 12.74/12.99      inference('cnf', [status(esa)], [cc1_relset_1])).
% 12.74/12.99  thf('67', plain, ((v1_relat_1 @ sk_E)),
% 12.74/12.99      inference('sup-', [status(thm)], ['65', '66'])).
% 12.74/12.99  thf('68', plain,
% 12.74/12.99      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 12.74/12.99          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 12.74/12.99        | ((sk_C) = (k1_xboole_0))
% 12.74/12.99        | (v1_xboole_0 @ sk_B)
% 12.74/12.99        | ((sk_C) = (k1_xboole_0)))),
% 12.74/12.99      inference('demod', [status(thm)], ['63', '64', '67'])).
% 12.74/12.99  thf('69', plain, (((v1_xboole_0 @ sk_B) | ((sk_C) = (k1_xboole_0)))),
% 12.74/12.99      inference('simplify', [status(thm)], ['68'])).
% 12.74/12.99  thf(l13_xboole_0, axiom,
% 12.74/12.99    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 12.74/12.99  thf('70', plain,
% 12.74/12.99      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 12.74/12.99      inference('cnf', [status(esa)], [l13_xboole_0])).
% 12.74/12.99  thf('71', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 12.74/12.99      inference('sup-', [status(thm)], ['69', '70'])).
% 12.74/12.99  thf('72', plain, (((sk_B) != (k1_xboole_0))),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf('73', plain, (((sk_C) = (k1_xboole_0))),
% 12.74/12.99      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 12.74/12.99  thf('74', plain,
% 12.74/12.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ k1_xboole_0)))),
% 12.74/12.99      inference('demod', [status(thm)], ['13', '73'])).
% 12.74/12.99  thf('75', plain,
% 12.74/12.99      (![X37 : $i, X38 : $i, X39 : $i]:
% 12.74/12.99         (((X37) != (k1_xboole_0))
% 12.74/12.99          | ((X38) = (k1_xboole_0))
% 12.74/12.99          | ((X39) = (k1_xboole_0))
% 12.74/12.99          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 12.74/12.99          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 12.74/12.99  thf('76', plain,
% 12.74/12.99      (![X38 : $i, X39 : $i]:
% 12.74/12.99         (~ (m1_subset_1 @ X39 @ 
% 12.74/12.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ k1_xboole_0)))
% 12.74/12.99          | ~ (v1_funct_2 @ X39 @ X38 @ k1_xboole_0)
% 12.74/12.99          | ((X39) = (k1_xboole_0))
% 12.74/12.99          | ((X38) = (k1_xboole_0)))),
% 12.74/12.99      inference('simplify', [status(thm)], ['75'])).
% 12.74/12.99  thf('77', plain,
% 12.74/12.99      ((((sk_B) = (k1_xboole_0))
% 12.74/12.99        | ((sk_D) = (k1_xboole_0))
% 12.74/12.99        | ~ (v1_funct_2 @ sk_D @ sk_B @ k1_xboole_0))),
% 12.74/12.99      inference('sup-', [status(thm)], ['74', '76'])).
% 12.74/12.99  thf('78', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf('79', plain, (((sk_C) = (k1_xboole_0))),
% 12.74/12.99      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 12.74/12.99  thf('80', plain, ((v1_funct_2 @ sk_D @ sk_B @ k1_xboole_0)),
% 12.74/12.99      inference('demod', [status(thm)], ['78', '79'])).
% 12.74/12.99  thf('81', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 12.74/12.99      inference('demod', [status(thm)], ['77', '80'])).
% 12.74/12.99  thf('82', plain, (((sk_B) != (k1_xboole_0))),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf('83', plain, (((sk_D) = (k1_xboole_0))),
% 12.74/12.99      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 12.74/12.99  thf('84', plain, (((sk_D) = (k1_xboole_0))),
% 12.74/12.99      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 12.74/12.99  thf('85', plain,
% 12.74/12.99      ((((k1_xboole_0) != (k1_xboole_0))
% 12.74/12.99        | (r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ sk_B))),
% 12.74/12.99      inference('demod', [status(thm)], ['12', '83', '84'])).
% 12.74/12.99  thf('86', plain, ((r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ sk_B)),
% 12.74/12.99      inference('simplify', [status(thm)], ['85'])).
% 12.74/12.99  thf(t69_xboole_1, axiom,
% 12.74/12.99    (![A:$i,B:$i]:
% 12.74/12.99     ( ( ~( v1_xboole_0 @ B ) ) =>
% 12.74/12.99       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 12.74/12.99  thf('87', plain,
% 12.74/12.99      (![X1 : $i, X2 : $i]:
% 12.74/12.99         (~ (r1_xboole_0 @ X1 @ X2)
% 12.74/12.99          | ~ (r1_tarski @ X1 @ X2)
% 12.74/12.99          | (v1_xboole_0 @ X1))),
% 12.74/12.99      inference('cnf', [status(esa)], [t69_xboole_1])).
% 12.74/12.99  thf('88', plain,
% 12.74/12.99      (((v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 12.74/12.99        | ~ (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ sk_B))),
% 12.74/12.99      inference('sup-', [status(thm)], ['86', '87'])).
% 12.74/12.99  thf('89', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 12.74/12.99      inference('sup-', [status(thm)], ['0', '1'])).
% 12.74/12.99  thf(d18_relat_1, axiom,
% 12.74/12.99    (![A:$i,B:$i]:
% 12.74/12.99     ( ( v1_relat_1 @ B ) =>
% 12.74/12.99       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 12.74/12.99  thf('90', plain,
% 12.74/12.99      (![X5 : $i, X6 : $i]:
% 12.74/12.99         (~ (v4_relat_1 @ X5 @ X6)
% 12.74/12.99          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 12.74/12.99          | ~ (v1_relat_1 @ X5))),
% 12.74/12.99      inference('cnf', [status(esa)], [d18_relat_1])).
% 12.74/12.99  thf('91', plain,
% 12.74/12.99      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 12.74/12.99      inference('sup-', [status(thm)], ['89', '90'])).
% 12.74/12.99  thf('92', plain, ((v1_relat_1 @ sk_D)),
% 12.74/12.99      inference('sup-', [status(thm)], ['5', '6'])).
% 12.74/12.99  thf('93', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 12.74/12.99      inference('demod', [status(thm)], ['91', '92'])).
% 12.74/12.99  thf('94', plain, (((sk_D) = (k1_xboole_0))),
% 12.74/12.99      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 12.74/12.99  thf('95', plain, ((r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ sk_B)),
% 12.74/12.99      inference('demod', [status(thm)], ['93', '94'])).
% 12.74/12.99  thf('96', plain, ((v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))),
% 12.74/12.99      inference('demod', [status(thm)], ['88', '95'])).
% 12.74/12.99  thf('97', plain,
% 12.74/12.99      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 12.74/12.99      inference('cnf', [status(esa)], [l13_xboole_0])).
% 12.74/12.99  thf('98', plain, (~ (v1_xboole_0 @ sk_C)),
% 12.74/12.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.74/12.99  thf('99', plain, (((sk_C) = (k1_xboole_0))),
% 12.74/12.99      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 12.74/12.99  thf('100', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 12.74/12.99      inference('demod', [status(thm)], ['98', '99'])).
% 12.74/12.99  thf('101', plain,
% 12.74/12.99      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 12.74/12.99      inference('sup-', [status(thm)], ['97', '100'])).
% 12.74/12.99  thf('102', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 12.74/12.99      inference('simplify', [status(thm)], ['101'])).
% 12.74/12.99  thf('103', plain, ($false), inference('sup-', [status(thm)], ['96', '102'])).
% 12.74/12.99  
% 12.74/12.99  % SZS output end Refutation
% 12.74/12.99  
% 12.74/12.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
