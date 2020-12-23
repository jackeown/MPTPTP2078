%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZRcZrNB5gp

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 153 expanded)
%              Number of leaves         :   37 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  651 (2050 expanded)
%              Number of equality atoms :   35 ( 117 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t85_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v2_funct_1 @ B )
       => ! [C: $i,D: $i] :
            ( ( ( r2_hidden @ C @ A )
              & ( r2_hidden @ D @ A )
              & ( ( k1_funct_1 @ B @ C )
                = ( k1_funct_1 @ B @ D ) ) )
           => ( C = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( v2_funct_1 @ B )
         => ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A )
                & ( ( k1_funct_1 @ B @ C )
                  = ( k1_funct_1 @ B @ D ) ) )
             => ( C = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t85_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X32 @ X33 )
        = X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X32 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('8',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['3','4','5','8'])).

thf(t54_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ! [B: $i] :
            ( ( ( v1_funct_1 @ B )
              & ( v1_relat_1 @ B ) )
           => ( ( B
                = ( k2_funct_1 @ A ) )
            <=> ( ! [C: $i,D: $i] :
                    ( ( ( ( D
                          = ( k1_funct_1 @ B @ C ) )
                        & ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) )
                     => ( ( C
                          = ( k1_funct_1 @ A @ D ) )
                        & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) )
                    & ( ( ( C
                          = ( k1_funct_1 @ A @ D ) )
                        & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) )
                     => ( ( D
                          = ( k1_funct_1 @ B @ C ) )
                        & ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) ) )
                & ( ( k1_relat_1 @ B )
                  = ( k2_relat_1 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_2 @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
        & ( C
          = ( k1_funct_1 @ A @ D ) ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_2 @ X15 @ X17 @ X18 )
      | ( X17
       != ( k1_funct_1 @ X18 @ X15 ) )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X15: $i,X18: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X18 ) )
      | ( zip_tseitin_2 @ X15 @ ( k1_funct_1 @ X18 @ X15 ) @ X18 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_funct_1 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    zip_tseitin_2 @ sk_C_1 @ ( k1_funct_1 @ sk_B @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['0','12'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('15',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_2 @ D @ C @ A )
       => ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
          & ( D
            = ( k1_funct_1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ D @ C @ B @ A )
       => ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
          & ( C
            = ( k1_funct_1 @ A @ D ) ) ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) )
        & ( D
          = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_9,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( B
                = ( k2_funct_1 @ A ) )
            <=> ( ( ( k1_relat_1 @ B )
                  = ( k2_relat_1 @ A ) )
                & ! [C: $i,D: $i] :
                    ( ( zip_tseitin_3 @ D @ C @ B @ A )
                    & ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X24: $i,X25: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ( X25
       != ( k2_funct_1 @ X24 ) )
      | ( zip_tseitin_3 @ X28 @ X27 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('17',plain,(
    ! [X24: $i,X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( zip_tseitin_3 @ X28 @ X27 @ ( k2_funct_1 @ X24 ) @ X24 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( v2_funct_1 @ X24 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_3 @ X2 @ X1 @ ( k2_funct_1 @ X0 ) @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_2 @ X19 @ X20 @ X21 )
      | ( X19
        = ( k1_funct_1 @ X22 @ X20 ) )
      | ~ ( zip_tseitin_3 @ X19 @ X20 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X2
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_C_1
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_C_1 ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( sk_C_1
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['24','25','26','31'])).

thf('33',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ ( k1_funct_1 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('35',plain,(
    zip_tseitin_2 @ sk_D_1 @ ( k1_funct_1 @ sk_B @ sk_D_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_funct_1 @ sk_B @ sk_C_1 )
    = ( k1_funct_1 @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    zip_tseitin_2 @ sk_D_1 @ ( k1_funct_1 @ sk_B @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X2
        = ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('39',plain,
    ( ( sk_D_1
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_C_1 ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['29','30'])).

thf('43',plain,
    ( sk_D_1
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_funct_1 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    sk_D_1 = sk_C_1 ),
    inference('sup+',[status(thm)],['32','43'])).

thf('45',plain,(
    sk_C_1 != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZRcZrNB5gp
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:17:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 60 iterations in 0.036s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.50  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.50  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $i > $o).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.20/0.50  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.50  thf(t85_funct_2, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.50       ( ( v2_funct_1 @ B ) =>
% 0.20/0.50         ( ![C:$i,D:$i]:
% 0.20/0.50           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.20/0.50               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.20/0.50             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.50            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.50          ( ( v2_funct_1 @ B ) =>
% 0.20/0.50            ( ![C:$i,D:$i]:
% 0.20/0.50              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.20/0.50                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.20/0.50                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t85_funct_2])).
% 0.20/0.50  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t67_funct_2, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.50       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X32 : $i, X33 : $i]:
% 0.20/0.50         (((k1_relset_1 @ X32 @ X32 @ X33) = (X32))
% 0.20/0.50          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))
% 0.20/0.50          | ~ (v1_funct_2 @ X33 @ X32 @ X32)
% 0.20/0.50          | ~ (v1_funct_1 @ X33))),
% 0.20/0.50      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      ((~ (v1_funct_1 @ sk_B)
% 0.20/0.50        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.20/0.50        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.50         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.20/0.50          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.50  thf('8', plain, (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.20/0.50  thf(t54_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.20/0.50       ( ( v2_funct_1 @ A ) =>
% 0.20/0.50         ( ![B:$i]:
% 0.20/0.50           ( ( ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) =>
% 0.20/0.50             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.20/0.50               ( ( ![C:$i,D:$i]:
% 0.20/0.50                   ( ( ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.20/0.50                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) =>
% 0.20/0.50                       ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.20/0.50                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) & 
% 0.20/0.50                     ( ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.20/0.50                         ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) =>
% 0.20/0.50                       ( ( ( D ) = ( k1_funct_1 @ B @ C ) ) & 
% 0.20/0.50                         ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) ) ) ) ) & 
% 0.20/0.50                 ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_1, axiom,
% 0.20/0.50    (![D:$i,C:$i,A:$i]:
% 0.20/0.50     ( ( zip_tseitin_2 @ D @ C @ A ) <=>
% 0.20/0.50       ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.50         ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ))).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.20/0.50         ((zip_tseitin_2 @ X15 @ X17 @ X18)
% 0.20/0.50          | ((X17) != (k1_funct_1 @ X18 @ X15))
% 0.20/0.50          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X18)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X15 : $i, X18 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X15 @ (k1_relat_1 @ X18))
% 0.20/0.50          | (zip_tseitin_2 @ X15 @ (k1_funct_1 @ X18 @ X15) @ X18))),
% 0.20/0.50      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.50          | (zip_tseitin_2 @ X0 @ (k1_funct_1 @ sk_B @ X0) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      ((zip_tseitin_2 @ sk_C_1 @ (k1_funct_1 @ sk_B @ sk_C_1) @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '12'])).
% 0.20/0.50  thf(dt_k2_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.50       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.20/0.50         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X4 : $i]:
% 0.20/0.50         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.20/0.50          | ~ (v1_funct_1 @ X4)
% 0.20/0.50          | ~ (v1_relat_1 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X4 : $i]:
% 0.20/0.50         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.20/0.50          | ~ (v1_funct_1 @ X4)
% 0.20/0.50          | ~ (v1_relat_1 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.20/0.50  thf(zf_stmt_2, type, zip_tseitin_3 : $i > $i > $i > $i > $o).
% 0.20/0.50  thf(zf_stmt_3, axiom,
% 0.20/0.50    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.50     ( ( zip_tseitin_3 @ D @ C @ B @ A ) <=>
% 0.20/0.50       ( ( zip_tseitin_2 @ D @ C @ A ) =>
% 0.20/0.50         ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.20/0.50           ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_4, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.20/0.50  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.20/0.50  thf(zf_stmt_6, axiom,
% 0.20/0.50    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.50     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.20/0.50       ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.20/0.50         ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.50           ( ( C ) = ( k1_funct_1 @ A @ D ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.50  thf(zf_stmt_8, axiom,
% 0.20/0.50    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.50     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.20/0.50       ( ( r2_hidden @ C @ ( k2_relat_1 @ A ) ) & 
% 0.20/0.50         ( ( D ) = ( k1_funct_1 @ B @ C ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_9, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.50       ( ( v2_funct_1 @ A ) =>
% 0.20/0.50         ( ![B:$i]:
% 0.20/0.50           ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50             ( ( ( B ) = ( k2_funct_1 @ A ) ) <=>
% 0.20/0.50               ( ( ( k1_relat_1 @ B ) = ( k2_relat_1 @ A ) ) & 
% 0.20/0.50                 ( ![C:$i,D:$i]:
% 0.20/0.50                   ( ( zip_tseitin_3 @ D @ C @ B @ A ) & 
% 0.20/0.50                     ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X24 : $i, X25 : $i, X27 : $i, X28 : $i]:
% 0.20/0.50         (~ (v2_funct_1 @ X24)
% 0.20/0.50          | ~ (v1_relat_1 @ X25)
% 0.20/0.50          | ~ (v1_funct_1 @ X25)
% 0.20/0.50          | ((X25) != (k2_funct_1 @ X24))
% 0.20/0.50          | (zip_tseitin_3 @ X28 @ X27 @ X25 @ X24)
% 0.20/0.50          | ~ (v1_funct_1 @ X24)
% 0.20/0.50          | ~ (v1_relat_1 @ X24))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X24 : $i, X27 : $i, X28 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X24)
% 0.20/0.50          | ~ (v1_funct_1 @ X24)
% 0.20/0.50          | (zip_tseitin_3 @ X28 @ X27 @ (k2_funct_1 @ X24) @ X24)
% 0.20/0.50          | ~ (v1_funct_1 @ (k2_funct_1 @ X24))
% 0.20/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X24))
% 0.20/0.50          | ~ (v2_funct_1 @ X24))),
% 0.20/0.50      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (v2_funct_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.50          | (zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.20/0.50          | ~ (v2_funct_1 @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (v2_funct_1 @ X0)
% 0.20/0.50          | (zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((zip_tseitin_3 @ X2 @ X1 @ (k2_funct_1 @ X0) @ X0)
% 0.20/0.50          | ~ (v2_funct_1 @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.50         (~ (zip_tseitin_2 @ X19 @ X20 @ X21)
% 0.20/0.50          | ((X19) = (k1_funct_1 @ X22 @ X20))
% 0.20/0.50          | ~ (zip_tseitin_3 @ X19 @ X20 @ X22 @ X21))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (v2_funct_1 @ X0)
% 0.20/0.50          | ((X2) = (k1_funct_1 @ (k2_funct_1 @ X0) @ X1))
% 0.20/0.50          | ~ (zip_tseitin_2 @ X2 @ X1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      ((((sk_C_1)
% 0.20/0.50          = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_C_1)))
% 0.20/0.50        | ~ (v2_funct_1 @ sk_B)
% 0.20/0.50        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.50        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '23'])).
% 0.20/0.50  thf('25', plain, ((v2_funct_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc2_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.50          | (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.50  thf(fc6_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.50  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (((sk_C_1)
% 0.20/0.50         = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_C_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['24', '25', '26', '31'])).
% 0.20/0.50  thf('33', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.50          | (zip_tseitin_2 @ X0 @ (k1_funct_1 @ sk_B @ X0) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '11'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      ((zip_tseitin_2 @ sk_D_1 @ (k1_funct_1 @ sk_B @ sk_D_1) @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (((k1_funct_1 @ sk_B @ sk_C_1) = (k1_funct_1 @ sk_B @ sk_D_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      ((zip_tseitin_2 @ sk_D_1 @ (k1_funct_1 @ sk_B @ sk_C_1) @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (v2_funct_1 @ X0)
% 0.20/0.50          | ((X2) = (k1_funct_1 @ (k2_funct_1 @ X0) @ X1))
% 0.20/0.50          | ~ (zip_tseitin_2 @ X2 @ X1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      ((((sk_D_1)
% 0.20/0.50          = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_C_1)))
% 0.20/0.50        | ~ (v2_funct_1 @ sk_B)
% 0.20/0.50        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.50        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain, ((v2_funct_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('41', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (((sk_D_1)
% 0.20/0.50         = (k1_funct_1 @ (k2_funct_1 @ sk_B) @ (k1_funct_1 @ sk_B @ sk_C_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.20/0.50  thf('44', plain, (((sk_D_1) = (sk_C_1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['32', '43'])).
% 0.20/0.50  thf('45', plain, (((sk_C_1) != (sk_D_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('46', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
