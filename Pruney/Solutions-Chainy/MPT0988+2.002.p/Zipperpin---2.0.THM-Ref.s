%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S1oYCphUtZ

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:52 EST 2020

% Result     : Theorem 13.92s
% Output     : Refutation 13.92s
% Verified   : 
% Statistics : Number of formulae       :  321 (21561 expanded)
%              Number of leaves         :   53 (6384 expanded)
%              Depth                    :   41
%              Number of atoms          : 3153 (652370 expanded)
%              Number of equality atoms :  236 (62064 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t34_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( v2_funct_1 @ C )
              & ! [E: $i,F: $i] :
                  ( ( ( ( r2_hidden @ F @ A )
                      & ( ( k1_funct_1 @ C @ F )
                        = E ) )
                   => ( ( r2_hidden @ E @ B )
                      & ( ( k1_funct_1 @ D @ E )
                        = F ) ) )
                  & ( ( ( r2_hidden @ E @ B )
                      & ( ( k1_funct_1 @ D @ E )
                        = F ) )
                   => ( ( r2_hidden @ F @ A )
                      & ( ( k1_funct_1 @ C @ F )
                        = E ) ) ) ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( v2_funct_1 @ C )
                & ! [E: $i,F: $i] :
                    ( ( ( ( r2_hidden @ F @ A )
                        & ( ( k1_funct_1 @ C @ F )
                          = E ) )
                     => ( ( r2_hidden @ E @ B )
                        & ( ( k1_funct_1 @ D @ E )
                          = F ) ) )
                    & ( ( ( r2_hidden @ E @ B )
                        & ( ( k1_funct_1 @ D @ E )
                          = F ) )
                     => ( ( r2_hidden @ F @ A )
                        & ( ( k1_funct_1 @ C @ F )
                          = E ) ) ) ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('5',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('14',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['16','23','26'])).

thf(t60_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k1_relat_1 @ A )
                = ( k2_relat_1 @ B ) )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i,D: $i] :
                  ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                    & ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) )
                 => ( ( ( k1_funct_1 @ A @ C )
                      = D )
                  <=> ( ( k1_funct_1 @ B @ D )
                      = C ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X14
        = ( k2_funct_1 @ X15 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X15 ) @ ( k1_relat_1 @ X14 ) )
      | ( ( k2_relat_1 @ X15 )
       != ( k1_relat_1 @ X14 ) )
      | ( ( k1_relat_1 @ X15 )
       != ( k2_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t60_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != ( k2_relat_1 @ sk_D_2 ) )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 ) @ ( k1_relat_1 @ sk_D_2 ) )
      | ( sk_D_2
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['16','23','26'])).

thf('31',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('36',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != ( k2_relat_1 @ sk_D_2 ) )
      | ( r2_hidden @ ( sk_D @ sk_D_2 @ X0 ) @ sk_B )
      | ( sk_D_2
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','36'])).

thf('38',plain,
    ( ( sk_A
     != ( k2_relat_1 @ sk_D_2 ) )
    | ( sk_D_2
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C_1 ) @ sk_B )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k2_relat_1 @ sk_C_1 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['13','37'])).

thf('39',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('45',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('47',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('48',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_A
     != ( k2_relat_1 @ sk_D_2 ) )
    | ( sk_D_2
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C_1 ) @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['38','39','40','45','50'])).

thf('52',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C_1 ) @ sk_B )
    | ( sk_D_2
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( sk_A
     != ( k2_relat_1 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    sk_D_2
 != ( k2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C_1 ) @ sk_B )
    | ( sk_A
     != ( k2_relat_1 @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('56',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X16 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('57',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('60',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['57','60'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('62',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('64',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_D_2 ) )
    | ( sk_A
      = ( k2_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(t5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_relat_1 @ C ) )
     => ( ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
          & ( ( k1_relat_1 @ C )
            = A ) )
       => ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
          & ( v1_funct_2 @ C @ A @ B )
          & ( v1_funct_1 @ C ) ) ) ) )).

thf(zf_stmt_6,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_2 @ D @ C @ B @ A ) ) )).

thf('66',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( zip_tseitin_2 @ X37 @ X38 @ X39 @ X40 )
      | ( r2_hidden @ X37 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('67',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('68',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X33 )
       != X34 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('69',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('77',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('79',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('80',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('81',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('82',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('83',plain,(
    ! [X36: $i] :
      ( ( v1_funct_2 @ X36 @ ( k1_relat_1 @ X36 ) @ ( k2_relat_1 @ X36 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['78','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('93',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('97',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('99',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('101',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('102',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('103',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('107',plain,
    ( sk_B
    = ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['99','106'])).

thf('108',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['77','107'])).

thf(zf_stmt_7,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_2 @ D @ C @ B @ A ) )
       => ( zip_tseitin_3 @ C @ B @ A ) ) ) )).

thf('109',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( ( k1_relat_1 @ X45 )
       != X44 )
      | ~ ( zip_tseitin_2 @ ( sk_D_1 @ X45 @ X46 @ X44 ) @ X45 @ X46 @ X44 )
      | ( zip_tseitin_3 @ X45 @ X46 @ X44 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('110',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_relat_1 @ X45 )
      | ~ ( v1_funct_1 @ X45 )
      | ( zip_tseitin_3 @ X45 @ X46 @ ( k1_relat_1 @ X45 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_1 @ X45 @ X46 @ ( k1_relat_1 @ X45 ) ) @ X45 @ X46 @ ( k1_relat_1 @ X45 ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
      | ( zip_tseitin_3 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['108','110'])).

thf('112',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['77','107'])).

thf('113',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['77','107'])).

thf('114',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X33 )
       != X34 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('116',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['116','117','118','119','120'])).

thf('122',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('124',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('125',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('127',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ( zip_tseitin_3 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['111','112','113','122','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) @ sk_B )
      | ( zip_tseitin_3 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','128'])).

thf('130',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['48','49'])).

thf('131',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('132',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('133',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('134',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X12 @ X11 ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['132','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['131','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['130','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('142',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('146',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('147',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X16 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('148',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('150',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('152',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('153',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['150','153'])).

thf('155',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('156',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['145','156'])).

thf('158',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('160',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('162',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['157','158','160','161','162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['144','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( sk_D_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','165'])).

thf('167',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k1_funct_1 @ sk_D_2 @ X48 )
        = X49 )
      | ( ( k1_funct_1 @ sk_C_1 @ X49 )
       != X48 )
      | ~ ( r2_hidden @ X49 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X49: $i] :
      ( ~ ( r2_hidden @ X49 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_2 @ ( k1_funct_1 @ sk_C_1 @ X49 ) )
        = X49 ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ( ( k1_funct_1 @ sk_D_2 @ ( k1_funct_1 @ sk_C_1 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( sk_D_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) ) ) )
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( sk_D_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['166','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( sk_D_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','165'])).

thf('171',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r2_hidden @ X48 @ sk_B )
      | ( ( k1_funct_1 @ sk_C_1 @ X49 )
       != X48 )
      | ~ ( r2_hidden @ X49 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X49: $i] :
      ( ~ ( r2_hidden @ X49 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X49 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( sk_D_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['170','172'])).

thf('174',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['16','23','26'])).

thf('175',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X12 @ X11 ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['34','35'])).

thf('178',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ ( k1_funct_1 @ sk_C_1 @ ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( sk_D_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) ) ) ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['173','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( sk_D_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) ) @ ( k2_relat_1 @ sk_D_2 ) )
      | ( zip_tseitin_3 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ( zip_tseitin_3 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['169','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( sk_D_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( zip_tseitin_2 @ X37 @ X38 @ X39 @ X40 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X38 @ X37 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ( zip_tseitin_2 @ ( sk_D_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ( zip_tseitin_3 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['111','112','113','122','127'])).

thf('186',plain,
    ( ( zip_tseitin_3 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_2 ) @ sk_B )
    | ( zip_tseitin_3 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    zip_tseitin_3 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_2 ) @ sk_B ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( zip_tseitin_3 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('189',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X16 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('191',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ ( k2_relat_1 @ sk_D_2 ) @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('193',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('194',plain,
    ( ( k2_relset_1 @ sk_B @ ( k2_relat_1 @ sk_D_2 ) @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['157','158','160','161','162','163'])).

thf('196',plain,
    ( ( k2_relset_1 @ sk_B @ ( k2_relat_1 @ sk_D_2 ) @ ( k2_funct_1 @ sk_C_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['191','196'])).

thf('198',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('199',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['65','199'])).

thf('201',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C_1 ) @ sk_B )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['54','200'])).

thf('202',plain,(
    r2_hidden @ ( sk_D @ sk_D_2 @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X47 )
        = X48 )
      | ( ( k1_funct_1 @ sk_D_2 @ X48 )
       != X47 )
      | ~ ( r2_hidden @ X48 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X48: $i] :
      ( ~ ( r2_hidden @ X48 @ sk_B )
      | ( ( k1_funct_1 @ sk_C_1 @ ( k1_funct_1 @ sk_D_2 @ X48 ) )
        = X48 ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C_1 ) ) )
    = ( sk_D @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['202','204'])).

thf('206',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['16','23','26'])).

thf('207',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['48','49'])).

thf('208',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X14
        = ( k2_funct_1 @ X15 ) )
      | ( ( k1_funct_1 @ X15 @ ( sk_C @ X14 @ X15 ) )
        = ( sk_D @ X14 @ X15 ) )
      | ( ( k1_funct_1 @ X14 @ ( sk_D @ X14 @ X15 ) )
        = ( sk_C @ X14 @ X15 ) )
      | ( ( k2_relat_1 @ X15 )
       != ( k1_relat_1 @ X14 ) )
      | ( ( k1_relat_1 @ X15 )
       != ( k2_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t60_funct_1])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( sk_B
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 )
      | ( ( k1_relat_1 @ sk_C_1 )
       != ( k2_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ ( sk_D @ X0 @ sk_C_1 ) )
        = ( sk_C @ X0 @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ X0 @ sk_C_1 ) )
        = ( sk_D @ X0 @ sk_C_1 ) )
      | ( X0
        = ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('211',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( sk_B
       != ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ sk_C_1 )
       != ( k2_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ ( sk_D @ X0 @ sk_C_1 ) )
        = ( sk_C @ X0 @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ X0 @ sk_C_1 ) )
        = ( sk_D @ X0 @ sk_C_1 ) )
      | ( X0
        = ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['209','210','211','212'])).

thf('214',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( sk_B
       != ( k1_relat_1 @ X0 ) )
      | ( sk_A
       != ( k2_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ ( sk_D @ X0 @ sk_C_1 ) )
        = ( sk_C @ X0 @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ X0 @ sk_C_1 ) )
        = ( sk_D @ X0 @ sk_C_1 ) )
      | ( X0
        = ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,
    ( ( sk_B != sk_B )
    | ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ( sk_D_2
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D_2 @ sk_C_1 ) )
      = ( sk_D @ sk_D_2 @ sk_C_1 ) )
    | ( ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C_1 ) )
      = ( sk_C @ sk_D_2 @ sk_C_1 ) )
    | ( sk_A
     != ( k2_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['206','215'])).

thf('217',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['34','35'])).

thf('218',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( sk_B != sk_B )
    | ( sk_D_2
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D_2 @ sk_C_1 ) )
      = ( sk_D @ sk_D_2 @ sk_C_1 ) )
    | ( ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C_1 ) )
      = ( sk_C @ sk_D_2 @ sk_C_1 ) )
    | ( sk_A
     != ( k2_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('220',plain,
    ( ( sk_A
     != ( k2_relat_1 @ sk_D_2 ) )
    | ( ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C_1 ) )
      = ( sk_C @ sk_D_2 @ sk_C_1 ) )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D_2 @ sk_C_1 ) )
      = ( sk_D @ sk_D_2 @ sk_C_1 ) )
    | ( sk_D_2
      = ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,(
    sk_D_2
 != ( k2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( sk_A
     != ( k2_relat_1 @ sk_D_2 ) )
    | ( ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C_1 ) )
      = ( sk_C @ sk_D_2 @ sk_C_1 ) )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D_2 @ sk_C_1 ) )
      = ( sk_D @ sk_D_2 @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['220','221'])).

thf('223',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['65','199'])).

thf('224',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C_1 ) )
      = ( sk_C @ sk_D_2 @ sk_C_1 ) )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D_2 @ sk_C_1 ) )
      = ( sk_D @ sk_D_2 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D_2 @ sk_C_1 ) )
      = ( sk_D @ sk_D_2 @ sk_C_1 ) )
    | ( ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C_1 ) )
      = ( sk_C @ sk_D_2 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['224'])).

thf('226',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['16','23','26'])).

thf('227',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['48','49'])).

thf('228',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X14
        = ( k2_funct_1 @ X15 ) )
      | ( r2_hidden @ ( sk_C @ X14 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ( ( k2_relat_1 @ X15 )
       != ( k1_relat_1 @ X14 ) )
      | ( ( k1_relat_1 @ X15 )
       != ( k2_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t60_funct_1])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( sk_B
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 )
      | ( ( k1_relat_1 @ sk_C_1 )
       != ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( X0
        = ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('231',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('234',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( sk_B
       != ( k1_relat_1 @ X0 ) )
      | ( sk_A
       != ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( X0
        = ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['229','230','231','232','233','234'])).

thf('236',plain,
    ( ( sk_B != sk_B )
    | ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ( sk_D_2
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_C_1 ) @ sk_A )
    | ( sk_A
     != ( k2_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['226','235'])).

thf('237',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['34','35'])).

thf('238',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( sk_B != sk_B )
    | ( sk_D_2
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_C_1 ) @ sk_A )
    | ( sk_A
     != ( k2_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['236','237','238'])).

thf('240',plain,
    ( ( sk_A
     != ( k2_relat_1 @ sk_D_2 ) )
    | ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_C_1 ) @ sk_A )
    | ( sk_D_2
      = ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['239'])).

thf('241',plain,(
    sk_D_2
 != ( k2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( sk_A
     != ( k2_relat_1 @ sk_D_2 ) )
    | ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_C_1 ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['240','241'])).

thf('243',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['65','199'])).

thf('244',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ ( sk_C @ sk_D_2 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['242','243'])).

thf('245',plain,(
    r2_hidden @ ( sk_C @ sk_D_2 @ sk_C_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['244'])).

thf('246',plain,(
    ! [X49: $i] :
      ( ~ ( r2_hidden @ X49 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_2 @ ( k1_funct_1 @ sk_C_1 @ X49 ) )
        = X49 ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('247',plain,
    ( ( k1_funct_1 @ sk_D_2 @ ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D_2 @ sk_C_1 ) ) )
    = ( sk_C @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,
    ( ( ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C_1 ) )
      = ( sk_C @ sk_D_2 @ sk_C_1 ) )
    | ( ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C_1 ) )
      = ( sk_C @ sk_D_2 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['225','247'])).

thf('249',plain,
    ( ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C_1 ) )
    = ( sk_C @ sk_D_2 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['248'])).

thf('250',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D_2 @ sk_C_1 ) )
    = ( sk_D @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['205','249'])).

thf('251',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X14
        = ( k2_funct_1 @ X15 ) )
      | ( ( k1_funct_1 @ X15 @ ( sk_C @ X14 @ X15 ) )
       != ( sk_D @ X14 @ X15 ) )
      | ( ( k1_funct_1 @ X14 @ ( sk_D @ X14 @ X15 ) )
       != ( sk_C @ X14 @ X15 ) )
      | ( ( k2_relat_1 @ X15 )
       != ( k1_relat_1 @ X14 ) )
      | ( ( k1_relat_1 @ X15 )
       != ( k2_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t60_funct_1])).

thf('252',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_C_1 )
     != ( sk_D @ sk_D_2 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k2_relat_1 @ sk_D_2 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D_2 ) )
    | ( ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C_1 ) )
     != ( sk_C @ sk_D_2 @ sk_C_1 ) )
    | ( sk_D_2
      = ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('254',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('257',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['65','199'])).

thf('258',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['48','49'])).

thf('259',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['16','23','26'])).

thf('260',plain,
    ( ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C_1 ) )
    = ( sk_C @ sk_D_2 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['248'])).

thf('261',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['34','35'])).

thf('263',plain,
    ( ( ( sk_D @ sk_D_2 @ sk_C_1 )
     != ( sk_D @ sk_D_2 @ sk_C_1 ) )
    | ( sk_A != sk_A )
    | ( sk_B != sk_B )
    | ( ( sk_C @ sk_D_2 @ sk_C_1 )
     != ( sk_C @ sk_D_2 @ sk_C_1 ) )
    | ( sk_D_2
      = ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['252','253','254','255','256','257','258','259','260','261','262'])).

thf('264',plain,
    ( sk_D_2
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['263'])).

thf('265',plain,(
    sk_D_2
 != ( k2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['264','265'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S1oYCphUtZ
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 13.92/14.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 13.92/14.12  % Solved by: fo/fo7.sh
% 13.92/14.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.92/14.12  % done 3105 iterations in 13.663s
% 13.92/14.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 13.92/14.12  % SZS output start Refutation
% 13.92/14.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 13.92/14.12  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 13.92/14.12  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 13.92/14.12  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 13.92/14.12  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 13.92/14.12  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 13.92/14.12  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 13.92/14.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 13.92/14.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 13.92/14.12  thf(sk_C_1_type, type, sk_C_1: $i).
% 13.92/14.12  thf(sk_B_type, type, sk_B: $i).
% 13.92/14.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 13.92/14.12  thf(sk_D_2_type, type, sk_D_2: $i).
% 13.92/14.12  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 13.92/14.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 13.92/14.12  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 13.92/14.12  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 13.92/14.12  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 13.92/14.12  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 13.92/14.12  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 13.92/14.12  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 13.92/14.12  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 13.92/14.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 13.92/14.12  thf(sk_A_type, type, sk_A: $i).
% 13.92/14.12  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 13.92/14.12  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 13.92/14.12  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 13.92/14.12  thf(t34_funct_2, conjecture,
% 13.92/14.12    (![A:$i,B:$i,C:$i]:
% 13.92/14.12     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 13.92/14.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 13.92/14.12       ( ![D:$i]:
% 13.92/14.12         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 13.92/14.12             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 13.92/14.12           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) & 
% 13.92/14.12               ( ![E:$i,F:$i]:
% 13.92/14.12                 ( ( ( ( r2_hidden @ F @ A ) & 
% 13.92/14.12                       ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) =>
% 13.92/14.12                     ( ( r2_hidden @ E @ B ) & 
% 13.92/14.12                       ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) ) & 
% 13.92/14.12                   ( ( ( r2_hidden @ E @ B ) & 
% 13.92/14.12                       ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) =>
% 13.92/14.12                     ( ( r2_hidden @ F @ A ) & 
% 13.92/14.12                       ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) ) ) ) ) =>
% 13.92/14.12             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 13.92/14.12               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 13.92/14.12  thf(zf_stmt_0, negated_conjecture,
% 13.92/14.12    (~( ![A:$i,B:$i,C:$i]:
% 13.92/14.12        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 13.92/14.12            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 13.92/14.12          ( ![D:$i]:
% 13.92/14.12            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 13.92/14.12                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 13.92/14.12              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 13.92/14.12                  ( v2_funct_1 @ C ) & 
% 13.92/14.12                  ( ![E:$i,F:$i]:
% 13.92/14.12                    ( ( ( ( r2_hidden @ F @ A ) & 
% 13.92/14.12                          ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) =>
% 13.92/14.12                        ( ( r2_hidden @ E @ B ) & 
% 13.92/14.12                          ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) ) & 
% 13.92/14.12                      ( ( ( r2_hidden @ E @ B ) & 
% 13.92/14.12                          ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) =>
% 13.92/14.12                        ( ( r2_hidden @ F @ A ) & 
% 13.92/14.12                          ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) ) ) ) ) =>
% 13.92/14.12                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 13.92/14.12                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 13.92/14.12    inference('cnf.neg', [status(esa)], [t34_funct_2])).
% 13.92/14.12  thf('0', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf(d1_funct_2, axiom,
% 13.92/14.12    (![A:$i,B:$i,C:$i]:
% 13.92/14.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.92/14.12       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 13.92/14.12           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 13.92/14.12             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 13.92/14.12         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 13.92/14.12           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 13.92/14.12             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 13.92/14.12  thf(zf_stmt_1, axiom,
% 13.92/14.12    (![C:$i,B:$i,A:$i]:
% 13.92/14.12     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 13.92/14.12       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 13.92/14.12  thf('1', plain,
% 13.92/14.12      (![X27 : $i, X28 : $i, X29 : $i]:
% 13.92/14.12         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 13.92/14.12          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 13.92/14.12          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 13.92/14.12  thf('2', plain,
% 13.92/14.12      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 13.92/14.12        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 13.92/14.12      inference('sup-', [status(thm)], ['0', '1'])).
% 13.92/14.12  thf(zf_stmt_2, axiom,
% 13.92/14.12    (![B:$i,A:$i]:
% 13.92/14.12     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 13.92/14.12       ( zip_tseitin_0 @ B @ A ) ))).
% 13.92/14.12  thf('3', plain,
% 13.92/14.12      (![X25 : $i, X26 : $i]:
% 13.92/14.12         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_2])).
% 13.92/14.12  thf('4', plain,
% 13.92/14.12      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 13.92/14.12  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 13.92/14.12  thf(zf_stmt_5, axiom,
% 13.92/14.12    (![A:$i,B:$i,C:$i]:
% 13.92/14.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.92/14.12       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 13.92/14.12         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 13.92/14.12           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 13.92/14.12             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 13.92/14.12  thf('5', plain,
% 13.92/14.12      (![X30 : $i, X31 : $i, X32 : $i]:
% 13.92/14.12         (~ (zip_tseitin_0 @ X30 @ X31)
% 13.92/14.12          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 13.92/14.12          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_5])).
% 13.92/14.12  thf('6', plain,
% 13.92/14.12      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 13.92/14.12        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 13.92/14.12      inference('sup-', [status(thm)], ['4', '5'])).
% 13.92/14.12  thf('7', plain,
% 13.92/14.12      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 13.92/14.12      inference('sup-', [status(thm)], ['3', '6'])).
% 13.92/14.12  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('9', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)),
% 13.92/14.12      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 13.92/14.12  thf('10', plain,
% 13.92/14.12      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf(redefinition_k1_relset_1, axiom,
% 13.92/14.12    (![A:$i,B:$i,C:$i]:
% 13.92/14.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.92/14.12       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 13.92/14.12  thf('11', plain,
% 13.92/14.12      (![X19 : $i, X20 : $i, X21 : $i]:
% 13.92/14.12         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 13.92/14.12          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 13.92/14.12      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 13.92/14.12  thf('12', plain,
% 13.92/14.12      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 13.92/14.12      inference('sup-', [status(thm)], ['10', '11'])).
% 13.92/14.12  thf('13', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 13.92/14.12      inference('demod', [status(thm)], ['2', '9', '12'])).
% 13.92/14.12  thf('14', plain, ((v1_funct_2 @ sk_D_2 @ sk_B @ sk_A)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('15', plain,
% 13.92/14.12      (![X27 : $i, X28 : $i, X29 : $i]:
% 13.92/14.12         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 13.92/14.12          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 13.92/14.12          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 13.92/14.12  thf('16', plain,
% 13.92/14.12      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_A @ sk_B)
% 13.92/14.12        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D_2)))),
% 13.92/14.12      inference('sup-', [status(thm)], ['14', '15'])).
% 13.92/14.12  thf('17', plain,
% 13.92/14.12      (![X25 : $i, X26 : $i]:
% 13.92/14.12         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_2])).
% 13.92/14.12  thf('18', plain,
% 13.92/14.12      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('19', plain,
% 13.92/14.12      (![X30 : $i, X31 : $i, X32 : $i]:
% 13.92/14.12         (~ (zip_tseitin_0 @ X30 @ X31)
% 13.92/14.12          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 13.92/14.12          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_5])).
% 13.92/14.12  thf('20', plain,
% 13.92/14.12      (((zip_tseitin_1 @ sk_D_2 @ sk_A @ sk_B)
% 13.92/14.12        | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 13.92/14.12      inference('sup-', [status(thm)], ['18', '19'])).
% 13.92/14.12  thf('21', plain,
% 13.92/14.12      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_2 @ sk_A @ sk_B))),
% 13.92/14.12      inference('sup-', [status(thm)], ['17', '20'])).
% 13.92/14.12  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('23', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_A @ sk_B)),
% 13.92/14.12      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 13.92/14.12  thf('24', plain,
% 13.92/14.12      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('25', plain,
% 13.92/14.12      (![X19 : $i, X20 : $i, X21 : $i]:
% 13.92/14.12         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 13.92/14.12          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 13.92/14.12      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 13.92/14.12  thf('26', plain,
% 13.92/14.12      (((k1_relset_1 @ sk_B @ sk_A @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 13.92/14.12      inference('sup-', [status(thm)], ['24', '25'])).
% 13.92/14.12  thf('27', plain, (((sk_B) = (k1_relat_1 @ sk_D_2))),
% 13.92/14.12      inference('demod', [status(thm)], ['16', '23', '26'])).
% 13.92/14.12  thf(t60_funct_1, axiom,
% 13.92/14.12    (![A:$i]:
% 13.92/14.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 13.92/14.12       ( ![B:$i]:
% 13.92/14.12         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 13.92/14.12           ( ( ( v2_funct_1 @ A ) & 
% 13.92/14.12               ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ B ) ) & 
% 13.92/14.12               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 13.92/14.12               ( ![C:$i,D:$i]:
% 13.92/14.12                 ( ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 13.92/14.12                     ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) ) =>
% 13.92/14.12                   ( ( ( k1_funct_1 @ A @ C ) = ( D ) ) <=>
% 13.92/14.12                     ( ( k1_funct_1 @ B @ D ) = ( C ) ) ) ) ) ) =>
% 13.92/14.12             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 13.92/14.12  thf('28', plain,
% 13.92/14.12      (![X14 : $i, X15 : $i]:
% 13.92/14.12         (~ (v1_relat_1 @ X14)
% 13.92/14.12          | ~ (v1_funct_1 @ X14)
% 13.92/14.12          | ((X14) = (k2_funct_1 @ X15))
% 13.92/14.12          | (r2_hidden @ (sk_D @ X14 @ X15) @ (k1_relat_1 @ X14))
% 13.92/14.12          | ((k2_relat_1 @ X15) != (k1_relat_1 @ X14))
% 13.92/14.12          | ((k1_relat_1 @ X15) != (k2_relat_1 @ X14))
% 13.92/14.12          | ~ (v2_funct_1 @ X15)
% 13.92/14.12          | ~ (v1_funct_1 @ X15)
% 13.92/14.12          | ~ (v1_relat_1 @ X15))),
% 13.92/14.12      inference('cnf', [status(esa)], [t60_funct_1])).
% 13.92/14.12  thf('29', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         (((k2_relat_1 @ X0) != (sk_B))
% 13.92/14.12          | ~ (v1_relat_1 @ X0)
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v2_funct_1 @ X0)
% 13.92/14.12          | ((k1_relat_1 @ X0) != (k2_relat_1 @ sk_D_2))
% 13.92/14.12          | (r2_hidden @ (sk_D @ sk_D_2 @ X0) @ (k1_relat_1 @ sk_D_2))
% 13.92/14.12          | ((sk_D_2) = (k2_funct_1 @ X0))
% 13.92/14.12          | ~ (v1_funct_1 @ sk_D_2)
% 13.92/14.12          | ~ (v1_relat_1 @ sk_D_2))),
% 13.92/14.12      inference('sup-', [status(thm)], ['27', '28'])).
% 13.92/14.12  thf('30', plain, (((sk_B) = (k1_relat_1 @ sk_D_2))),
% 13.92/14.12      inference('demod', [status(thm)], ['16', '23', '26'])).
% 13.92/14.12  thf('31', plain, ((v1_funct_1 @ sk_D_2)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('32', plain,
% 13.92/14.12      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf(cc2_relat_1, axiom,
% 13.92/14.12    (![A:$i]:
% 13.92/14.12     ( ( v1_relat_1 @ A ) =>
% 13.92/14.12       ( ![B:$i]:
% 13.92/14.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 13.92/14.12  thf('33', plain,
% 13.92/14.12      (![X6 : $i, X7 : $i]:
% 13.92/14.12         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 13.92/14.12          | (v1_relat_1 @ X6)
% 13.92/14.12          | ~ (v1_relat_1 @ X7))),
% 13.92/14.12      inference('cnf', [status(esa)], [cc2_relat_1])).
% 13.92/14.12  thf('34', plain,
% 13.92/14.12      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D_2))),
% 13.92/14.12      inference('sup-', [status(thm)], ['32', '33'])).
% 13.92/14.12  thf(fc6_relat_1, axiom,
% 13.92/14.12    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 13.92/14.12  thf('35', plain,
% 13.92/14.12      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 13.92/14.12      inference('cnf', [status(esa)], [fc6_relat_1])).
% 13.92/14.12  thf('36', plain, ((v1_relat_1 @ sk_D_2)),
% 13.92/14.12      inference('demod', [status(thm)], ['34', '35'])).
% 13.92/14.12  thf('37', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         (((k2_relat_1 @ X0) != (sk_B))
% 13.92/14.12          | ~ (v1_relat_1 @ X0)
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v2_funct_1 @ X0)
% 13.92/14.12          | ((k1_relat_1 @ X0) != (k2_relat_1 @ sk_D_2))
% 13.92/14.12          | (r2_hidden @ (sk_D @ sk_D_2 @ X0) @ sk_B)
% 13.92/14.12          | ((sk_D_2) = (k2_funct_1 @ X0)))),
% 13.92/14.12      inference('demod', [status(thm)], ['29', '30', '31', '36'])).
% 13.92/14.12  thf('38', plain,
% 13.92/14.12      ((((sk_A) != (k2_relat_1 @ sk_D_2))
% 13.92/14.12        | ((sk_D_2) = (k2_funct_1 @ sk_C_1))
% 13.92/14.12        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_C_1) @ sk_B)
% 13.92/14.12        | ~ (v2_funct_1 @ sk_C_1)
% 13.92/14.12        | ~ (v1_funct_1 @ sk_C_1)
% 13.92/14.12        | ~ (v1_relat_1 @ sk_C_1)
% 13.92/14.12        | ((k2_relat_1 @ sk_C_1) != (sk_B)))),
% 13.92/14.12      inference('sup-', [status(thm)], ['13', '37'])).
% 13.92/14.12  thf('39', plain, ((v2_funct_1 @ sk_C_1)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('40', plain, ((v1_funct_1 @ sk_C_1)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('41', plain,
% 13.92/14.12      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('42', plain,
% 13.92/14.12      (![X6 : $i, X7 : $i]:
% 13.92/14.12         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 13.92/14.12          | (v1_relat_1 @ X6)
% 13.92/14.12          | ~ (v1_relat_1 @ X7))),
% 13.92/14.12      inference('cnf', [status(esa)], [cc2_relat_1])).
% 13.92/14.12  thf('43', plain,
% 13.92/14.12      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 13.92/14.12      inference('sup-', [status(thm)], ['41', '42'])).
% 13.92/14.12  thf('44', plain,
% 13.92/14.12      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 13.92/14.12      inference('cnf', [status(esa)], [fc6_relat_1])).
% 13.92/14.12  thf('45', plain, ((v1_relat_1 @ sk_C_1)),
% 13.92/14.12      inference('demod', [status(thm)], ['43', '44'])).
% 13.92/14.12  thf('46', plain,
% 13.92/14.12      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf(redefinition_k2_relset_1, axiom,
% 13.92/14.12    (![A:$i,B:$i,C:$i]:
% 13.92/14.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.92/14.12       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 13.92/14.12  thf('47', plain,
% 13.92/14.12      (![X22 : $i, X23 : $i, X24 : $i]:
% 13.92/14.12         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 13.92/14.12          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 13.92/14.12      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 13.92/14.12  thf('48', plain,
% 13.92/14.12      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 13.92/14.12      inference('sup-', [status(thm)], ['46', '47'])).
% 13.92/14.12  thf('49', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('50', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 13.92/14.12      inference('sup+', [status(thm)], ['48', '49'])).
% 13.92/14.12  thf('51', plain,
% 13.92/14.12      ((((sk_A) != (k2_relat_1 @ sk_D_2))
% 13.92/14.12        | ((sk_D_2) = (k2_funct_1 @ sk_C_1))
% 13.92/14.12        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_C_1) @ sk_B)
% 13.92/14.12        | ((sk_B) != (sk_B)))),
% 13.92/14.12      inference('demod', [status(thm)], ['38', '39', '40', '45', '50'])).
% 13.92/14.12  thf('52', plain,
% 13.92/14.12      (((r2_hidden @ (sk_D @ sk_D_2 @ sk_C_1) @ sk_B)
% 13.92/14.12        | ((sk_D_2) = (k2_funct_1 @ sk_C_1))
% 13.92/14.12        | ((sk_A) != (k2_relat_1 @ sk_D_2)))),
% 13.92/14.12      inference('simplify', [status(thm)], ['51'])).
% 13.92/14.12  thf('53', plain, (((sk_D_2) != (k2_funct_1 @ sk_C_1))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('54', plain,
% 13.92/14.12      (((r2_hidden @ (sk_D @ sk_D_2 @ sk_C_1) @ sk_B)
% 13.92/14.12        | ((sk_A) != (k2_relat_1 @ sk_D_2)))),
% 13.92/14.12      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 13.92/14.12  thf('55', plain,
% 13.92/14.12      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf(dt_k2_relset_1, axiom,
% 13.92/14.12    (![A:$i,B:$i,C:$i]:
% 13.92/14.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.92/14.12       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 13.92/14.12  thf('56', plain,
% 13.92/14.12      (![X16 : $i, X17 : $i, X18 : $i]:
% 13.92/14.12         ((m1_subset_1 @ (k2_relset_1 @ X16 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 13.92/14.12          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 13.92/14.12      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 13.92/14.12  thf('57', plain,
% 13.92/14.12      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_D_2) @ 
% 13.92/14.12        (k1_zfmisc_1 @ sk_A))),
% 13.92/14.12      inference('sup-', [status(thm)], ['55', '56'])).
% 13.92/14.12  thf('58', plain,
% 13.92/14.12      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('59', plain,
% 13.92/14.12      (![X22 : $i, X23 : $i, X24 : $i]:
% 13.92/14.12         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 13.92/14.12          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 13.92/14.12      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 13.92/14.12  thf('60', plain,
% 13.92/14.12      (((k2_relset_1 @ sk_B @ sk_A @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 13.92/14.12      inference('sup-', [status(thm)], ['58', '59'])).
% 13.92/14.12  thf('61', plain,
% 13.92/14.12      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ (k1_zfmisc_1 @ sk_A))),
% 13.92/14.12      inference('demod', [status(thm)], ['57', '60'])).
% 13.92/14.12  thf(t3_subset, axiom,
% 13.92/14.12    (![A:$i,B:$i]:
% 13.92/14.12     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 13.92/14.12  thf('62', plain,
% 13.92/14.12      (![X3 : $i, X4 : $i]:
% 13.92/14.12         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 13.92/14.12      inference('cnf', [status(esa)], [t3_subset])).
% 13.92/14.12  thf('63', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_A)),
% 13.92/14.12      inference('sup-', [status(thm)], ['61', '62'])).
% 13.92/14.12  thf(d10_xboole_0, axiom,
% 13.92/14.12    (![A:$i,B:$i]:
% 13.92/14.12     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 13.92/14.12  thf('64', plain,
% 13.92/14.12      (![X0 : $i, X2 : $i]:
% 13.92/14.12         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 13.92/14.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.92/14.12  thf('65', plain,
% 13.92/14.12      ((~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_D_2))
% 13.92/14.12        | ((sk_A) = (k2_relat_1 @ sk_D_2)))),
% 13.92/14.12      inference('sup-', [status(thm)], ['63', '64'])).
% 13.92/14.12  thf(t5_funct_2, axiom,
% 13.92/14.12    (![A:$i,B:$i,C:$i]:
% 13.92/14.12     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 13.92/14.12       ( ( ( ![D:$i]:
% 13.92/14.12             ( ( r2_hidden @ D @ A ) =>
% 13.92/14.12               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 13.92/14.12           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 13.92/14.12         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 13.92/14.12           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 13.92/14.12  thf(zf_stmt_6, axiom,
% 13.92/14.12    (![D:$i,C:$i,B:$i,A:$i]:
% 13.92/14.12     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 13.92/14.12       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 13.92/14.12  thf('66', plain,
% 13.92/14.12      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 13.92/14.12         ((zip_tseitin_2 @ X37 @ X38 @ X39 @ X40) | (r2_hidden @ X37 @ X40))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_6])).
% 13.92/14.12  thf('67', plain,
% 13.92/14.12      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf(t31_funct_2, axiom,
% 13.92/14.12    (![A:$i,B:$i,C:$i]:
% 13.92/14.12     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 13.92/14.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 13.92/14.12       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 13.92/14.12         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 13.92/14.12           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 13.92/14.12           ( m1_subset_1 @
% 13.92/14.12             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 13.92/14.12  thf('68', plain,
% 13.92/14.12      (![X33 : $i, X34 : $i, X35 : $i]:
% 13.92/14.12         (~ (v2_funct_1 @ X33)
% 13.92/14.12          | ((k2_relset_1 @ X35 @ X34 @ X33) != (X34))
% 13.92/14.12          | (m1_subset_1 @ (k2_funct_1 @ X33) @ 
% 13.92/14.12             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 13.92/14.12          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 13.92/14.12          | ~ (v1_funct_2 @ X33 @ X35 @ X34)
% 13.92/14.12          | ~ (v1_funct_1 @ X33))),
% 13.92/14.12      inference('cnf', [status(esa)], [t31_funct_2])).
% 13.92/14.12  thf('69', plain,
% 13.92/14.12      ((~ (v1_funct_1 @ sk_C_1)
% 13.92/14.12        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 13.92/14.12        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 13.92/14.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 13.92/14.12        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 13.92/14.12        | ~ (v2_funct_1 @ sk_C_1))),
% 13.92/14.12      inference('sup-', [status(thm)], ['67', '68'])).
% 13.92/14.12  thf('70', plain, ((v1_funct_1 @ sk_C_1)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('71', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('72', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('73', plain, ((v2_funct_1 @ sk_C_1)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('74', plain,
% 13.92/14.12      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 13.92/14.12         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 13.92/14.12        | ((sk_B) != (sk_B)))),
% 13.92/14.12      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 13.92/14.12  thf('75', plain,
% 13.92/14.12      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 13.92/14.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 13.92/14.12      inference('simplify', [status(thm)], ['74'])).
% 13.92/14.12  thf('76', plain,
% 13.92/14.12      (![X19 : $i, X20 : $i, X21 : $i]:
% 13.92/14.12         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 13.92/14.12          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 13.92/14.12      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 13.92/14.12  thf('77', plain,
% 13.92/14.12      (((k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C_1))
% 13.92/14.12         = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 13.92/14.12      inference('sup-', [status(thm)], ['75', '76'])).
% 13.92/14.12  thf('78', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 13.92/14.12      inference('sup+', [status(thm)], ['48', '49'])).
% 13.92/14.12  thf(t55_funct_1, axiom,
% 13.92/14.12    (![A:$i]:
% 13.92/14.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 13.92/14.12       ( ( v2_funct_1 @ A ) =>
% 13.92/14.12         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 13.92/14.12           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 13.92/14.12  thf('79', plain,
% 13.92/14.12      (![X13 : $i]:
% 13.92/14.12         (~ (v2_funct_1 @ X13)
% 13.92/14.12          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 13.92/14.12          | ~ (v1_funct_1 @ X13)
% 13.92/14.12          | ~ (v1_relat_1 @ X13))),
% 13.92/14.12      inference('cnf', [status(esa)], [t55_funct_1])).
% 13.92/14.12  thf(dt_k2_funct_1, axiom,
% 13.92/14.12    (![A:$i]:
% 13.92/14.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 13.92/14.12       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 13.92/14.12         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 13.92/14.12  thf('80', plain,
% 13.92/14.12      (![X10 : $i]:
% 13.92/14.12         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 13.92/14.12          | ~ (v1_funct_1 @ X10)
% 13.92/14.12          | ~ (v1_relat_1 @ X10))),
% 13.92/14.12      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 13.92/14.12  thf('81', plain,
% 13.92/14.12      (![X10 : $i]:
% 13.92/14.12         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 13.92/14.12          | ~ (v1_funct_1 @ X10)
% 13.92/14.12          | ~ (v1_relat_1 @ X10))),
% 13.92/14.12      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 13.92/14.12  thf('82', plain,
% 13.92/14.12      (![X13 : $i]:
% 13.92/14.12         (~ (v2_funct_1 @ X13)
% 13.92/14.12          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 13.92/14.12          | ~ (v1_funct_1 @ X13)
% 13.92/14.12          | ~ (v1_relat_1 @ X13))),
% 13.92/14.12      inference('cnf', [status(esa)], [t55_funct_1])).
% 13.92/14.12  thf(t3_funct_2, axiom,
% 13.92/14.12    (![A:$i]:
% 13.92/14.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 13.92/14.12       ( ( v1_funct_1 @ A ) & 
% 13.92/14.12         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 13.92/14.12         ( m1_subset_1 @
% 13.92/14.12           A @ 
% 13.92/14.12           ( k1_zfmisc_1 @
% 13.92/14.12             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 13.92/14.12  thf('83', plain,
% 13.92/14.12      (![X36 : $i]:
% 13.92/14.12         ((v1_funct_2 @ X36 @ (k1_relat_1 @ X36) @ (k2_relat_1 @ X36))
% 13.92/14.12          | ~ (v1_funct_1 @ X36)
% 13.92/14.12          | ~ (v1_relat_1 @ X36))),
% 13.92/14.12      inference('cnf', [status(esa)], [t3_funct_2])).
% 13.92/14.12  thf('84', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 13.92/14.12           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 13.92/14.12          | ~ (v1_relat_1 @ X0)
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v2_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 13.92/14.12          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 13.92/14.12      inference('sup+', [status(thm)], ['82', '83'])).
% 13.92/14.12  thf('85', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         (~ (v1_relat_1 @ X0)
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 13.92/14.12          | ~ (v2_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_relat_1 @ X0)
% 13.92/14.12          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 13.92/14.12             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 13.92/14.12      inference('sup-', [status(thm)], ['81', '84'])).
% 13.92/14.12  thf('86', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 13.92/14.12           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 13.92/14.12          | ~ (v2_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_relat_1 @ X0))),
% 13.92/14.12      inference('simplify', [status(thm)], ['85'])).
% 13.92/14.12  thf('87', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         (~ (v1_relat_1 @ X0)
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_relat_1 @ X0)
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v2_funct_1 @ X0)
% 13.92/14.12          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 13.92/14.12             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 13.92/14.12      inference('sup-', [status(thm)], ['80', '86'])).
% 13.92/14.12  thf('88', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 13.92/14.12           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 13.92/14.12          | ~ (v2_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_relat_1 @ X0))),
% 13.92/14.12      inference('simplify', [status(thm)], ['87'])).
% 13.92/14.12  thf('89', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 13.92/14.12           (k1_relat_1 @ X0))
% 13.92/14.12          | ~ (v1_relat_1 @ X0)
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v2_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_relat_1 @ X0)
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v2_funct_1 @ X0))),
% 13.92/14.12      inference('sup+', [status(thm)], ['79', '88'])).
% 13.92/14.12  thf('90', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         (~ (v2_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_relat_1 @ X0)
% 13.92/14.12          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 13.92/14.12             (k1_relat_1 @ X0)))),
% 13.92/14.12      inference('simplify', [status(thm)], ['89'])).
% 13.92/14.12  thf('91', plain,
% 13.92/14.12      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ (k1_relat_1 @ sk_C_1))
% 13.92/14.12        | ~ (v1_relat_1 @ sk_C_1)
% 13.92/14.12        | ~ (v1_funct_1 @ sk_C_1)
% 13.92/14.12        | ~ (v2_funct_1 @ sk_C_1))),
% 13.92/14.12      inference('sup+', [status(thm)], ['78', '90'])).
% 13.92/14.12  thf('92', plain, ((v1_relat_1 @ sk_C_1)),
% 13.92/14.12      inference('demod', [status(thm)], ['43', '44'])).
% 13.92/14.12  thf('93', plain, ((v1_funct_1 @ sk_C_1)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('94', plain, ((v2_funct_1 @ sk_C_1)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('95', plain,
% 13.92/14.12      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ (k1_relat_1 @ sk_C_1))),
% 13.92/14.12      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 13.92/14.12  thf('96', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 13.92/14.12      inference('demod', [status(thm)], ['2', '9', '12'])).
% 13.92/14.12  thf('97', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)),
% 13.92/14.12      inference('demod', [status(thm)], ['95', '96'])).
% 13.92/14.12  thf('98', plain,
% 13.92/14.12      (![X27 : $i, X28 : $i, X29 : $i]:
% 13.92/14.12         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 13.92/14.12          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 13.92/14.12          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 13.92/14.12  thf('99', plain,
% 13.92/14.12      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ sk_A @ sk_B)
% 13.92/14.12        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C_1))))),
% 13.92/14.12      inference('sup-', [status(thm)], ['97', '98'])).
% 13.92/14.12  thf('100', plain,
% 13.92/14.12      (![X25 : $i, X26 : $i]:
% 13.92/14.12         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_2])).
% 13.92/14.12  thf('101', plain,
% 13.92/14.12      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 13.92/14.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 13.92/14.12      inference('simplify', [status(thm)], ['74'])).
% 13.92/14.12  thf('102', plain,
% 13.92/14.12      (![X30 : $i, X31 : $i, X32 : $i]:
% 13.92/14.12         (~ (zip_tseitin_0 @ X30 @ X31)
% 13.92/14.12          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 13.92/14.12          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_5])).
% 13.92/14.12  thf('103', plain,
% 13.92/14.12      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ sk_A @ sk_B)
% 13.92/14.12        | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 13.92/14.12      inference('sup-', [status(thm)], ['101', '102'])).
% 13.92/14.12  thf('104', plain,
% 13.92/14.12      ((((sk_A) = (k1_xboole_0))
% 13.92/14.12        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ sk_A @ sk_B))),
% 13.92/14.12      inference('sup-', [status(thm)], ['100', '103'])).
% 13.92/14.12  thf('105', plain, (((sk_A) != (k1_xboole_0))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('106', plain, ((zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ sk_A @ sk_B)),
% 13.92/14.12      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 13.92/14.12  thf('107', plain,
% 13.92/14.12      (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C_1)))),
% 13.92/14.12      inference('demod', [status(thm)], ['99', '106'])).
% 13.92/14.12  thf('108', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 13.92/14.12      inference('sup+', [status(thm)], ['77', '107'])).
% 13.92/14.12  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $o).
% 13.92/14.12  thf(zf_stmt_8, axiom,
% 13.92/14.12    (![C:$i,B:$i,A:$i]:
% 13.92/14.12     ( ( zip_tseitin_3 @ C @ B @ A ) =>
% 13.92/14.12       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 13.92/14.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 13.92/14.12  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 13.92/14.12  thf(zf_stmt_10, axiom,
% 13.92/14.12    (![A:$i,B:$i,C:$i]:
% 13.92/14.12     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 13.92/14.12       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 13.92/14.12           ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) =>
% 13.92/14.12         ( zip_tseitin_3 @ C @ B @ A ) ) ))).
% 13.92/14.12  thf('109', plain,
% 13.92/14.12      (![X44 : $i, X45 : $i, X46 : $i]:
% 13.92/14.12         (((k1_relat_1 @ X45) != (X44))
% 13.92/14.12          | ~ (zip_tseitin_2 @ (sk_D_1 @ X45 @ X46 @ X44) @ X45 @ X46 @ X44)
% 13.92/14.12          | (zip_tseitin_3 @ X45 @ X46 @ X44)
% 13.92/14.12          | ~ (v1_funct_1 @ X45)
% 13.92/14.12          | ~ (v1_relat_1 @ X45))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_10])).
% 13.92/14.12  thf('110', plain,
% 13.92/14.12      (![X45 : $i, X46 : $i]:
% 13.92/14.12         (~ (v1_relat_1 @ X45)
% 13.92/14.12          | ~ (v1_funct_1 @ X45)
% 13.92/14.12          | (zip_tseitin_3 @ X45 @ X46 @ (k1_relat_1 @ X45))
% 13.92/14.12          | ~ (zip_tseitin_2 @ (sk_D_1 @ X45 @ X46 @ (k1_relat_1 @ X45)) @ 
% 13.92/14.12               X45 @ X46 @ (k1_relat_1 @ X45)))),
% 13.92/14.12      inference('simplify', [status(thm)], ['109'])).
% 13.92/14.12  thf('111', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         (~ (zip_tseitin_2 @ (sk_D_1 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B) @ 
% 13.92/14.12             (k2_funct_1 @ sk_C_1) @ X0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 13.92/14.12          | (zip_tseitin_3 @ (k2_funct_1 @ sk_C_1) @ X0 @ 
% 13.92/14.12             (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 13.92/14.12          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 13.92/14.12          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 13.92/14.12      inference('sup-', [status(thm)], ['108', '110'])).
% 13.92/14.12  thf('112', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 13.92/14.12      inference('sup+', [status(thm)], ['77', '107'])).
% 13.92/14.12  thf('113', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 13.92/14.12      inference('sup+', [status(thm)], ['77', '107'])).
% 13.92/14.12  thf('114', plain,
% 13.92/14.12      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('115', plain,
% 13.92/14.12      (![X33 : $i, X34 : $i, X35 : $i]:
% 13.92/14.12         (~ (v2_funct_1 @ X33)
% 13.92/14.12          | ((k2_relset_1 @ X35 @ X34 @ X33) != (X34))
% 13.92/14.12          | (v1_funct_1 @ (k2_funct_1 @ X33))
% 13.92/14.12          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 13.92/14.12          | ~ (v1_funct_2 @ X33 @ X35 @ X34)
% 13.92/14.12          | ~ (v1_funct_1 @ X33))),
% 13.92/14.12      inference('cnf', [status(esa)], [t31_funct_2])).
% 13.92/14.12  thf('116', plain,
% 13.92/14.12      ((~ (v1_funct_1 @ sk_C_1)
% 13.92/14.12        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 13.92/14.12        | (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 13.92/14.12        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 13.92/14.12        | ~ (v2_funct_1 @ sk_C_1))),
% 13.92/14.12      inference('sup-', [status(thm)], ['114', '115'])).
% 13.92/14.12  thf('117', plain, ((v1_funct_1 @ sk_C_1)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('118', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('119', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('120', plain, ((v2_funct_1 @ sk_C_1)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('121', plain,
% 13.92/14.12      (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)) | ((sk_B) != (sk_B)))),
% 13.92/14.12      inference('demod', [status(thm)], ['116', '117', '118', '119', '120'])).
% 13.92/14.12  thf('122', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 13.92/14.12      inference('simplify', [status(thm)], ['121'])).
% 13.92/14.12  thf('123', plain,
% 13.92/14.12      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 13.92/14.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 13.92/14.12      inference('simplify', [status(thm)], ['74'])).
% 13.92/14.12  thf('124', plain,
% 13.92/14.12      (![X6 : $i, X7 : $i]:
% 13.92/14.12         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 13.92/14.12          | (v1_relat_1 @ X6)
% 13.92/14.12          | ~ (v1_relat_1 @ X7))),
% 13.92/14.12      inference('cnf', [status(esa)], [cc2_relat_1])).
% 13.92/14.12  thf('125', plain,
% 13.92/14.12      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))
% 13.92/14.12        | (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 13.92/14.12      inference('sup-', [status(thm)], ['123', '124'])).
% 13.92/14.12  thf('126', plain,
% 13.92/14.12      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 13.92/14.12      inference('cnf', [status(esa)], [fc6_relat_1])).
% 13.92/14.12  thf('127', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 13.92/14.12      inference('demod', [status(thm)], ['125', '126'])).
% 13.92/14.12  thf('128', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         (~ (zip_tseitin_2 @ (sk_D_1 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B) @ 
% 13.92/14.12             (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)
% 13.92/14.12          | (zip_tseitin_3 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B))),
% 13.92/14.12      inference('demod', [status(thm)], ['111', '112', '113', '122', '127'])).
% 13.92/14.12  thf('129', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         ((r2_hidden @ (sk_D_1 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B) @ sk_B)
% 13.92/14.12          | (zip_tseitin_3 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B))),
% 13.92/14.12      inference('sup-', [status(thm)], ['66', '128'])).
% 13.92/14.12  thf('130', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 13.92/14.12      inference('sup+', [status(thm)], ['48', '49'])).
% 13.92/14.12  thf('131', plain,
% 13.92/14.12      (![X10 : $i]:
% 13.92/14.12         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 13.92/14.12          | ~ (v1_funct_1 @ X10)
% 13.92/14.12          | ~ (v1_relat_1 @ X10))),
% 13.92/14.12      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 13.92/14.12  thf('132', plain,
% 13.92/14.12      (![X10 : $i]:
% 13.92/14.12         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 13.92/14.12          | ~ (v1_funct_1 @ X10)
% 13.92/14.12          | ~ (v1_relat_1 @ X10))),
% 13.92/14.12      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 13.92/14.12  thf('133', plain,
% 13.92/14.12      (![X13 : $i]:
% 13.92/14.12         (~ (v2_funct_1 @ X13)
% 13.92/14.12          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 13.92/14.12          | ~ (v1_funct_1 @ X13)
% 13.92/14.12          | ~ (v1_relat_1 @ X13))),
% 13.92/14.12      inference('cnf', [status(esa)], [t55_funct_1])).
% 13.92/14.12  thf(t12_funct_1, axiom,
% 13.92/14.12    (![A:$i,B:$i]:
% 13.92/14.12     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 13.92/14.12       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 13.92/14.12         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 13.92/14.12  thf('134', plain,
% 13.92/14.12      (![X11 : $i, X12 : $i]:
% 13.92/14.12         (~ (r2_hidden @ X11 @ (k1_relat_1 @ X12))
% 13.92/14.12          | (r2_hidden @ (k1_funct_1 @ X12 @ X11) @ (k2_relat_1 @ X12))
% 13.92/14.12          | ~ (v1_funct_1 @ X12)
% 13.92/14.12          | ~ (v1_relat_1 @ X12))),
% 13.92/14.12      inference('cnf', [status(esa)], [t12_funct_1])).
% 13.92/14.12  thf('135', plain,
% 13.92/14.12      (![X0 : $i, X1 : $i]:
% 13.92/14.12         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 13.92/14.12          | ~ (v1_relat_1 @ X0)
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v2_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 13.92/14.12          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 13.92/14.12          | (r2_hidden @ (k1_funct_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 13.92/14.12             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 13.92/14.12      inference('sup-', [status(thm)], ['133', '134'])).
% 13.92/14.12  thf('136', plain,
% 13.92/14.12      (![X0 : $i, X1 : $i]:
% 13.92/14.12         (~ (v1_relat_1 @ X0)
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | (r2_hidden @ (k1_funct_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 13.92/14.12             (k2_relat_1 @ (k2_funct_1 @ X0)))
% 13.92/14.12          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 13.92/14.12          | ~ (v2_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_relat_1 @ X0)
% 13.92/14.12          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 13.92/14.12      inference('sup-', [status(thm)], ['132', '135'])).
% 13.92/14.12  thf('137', plain,
% 13.92/14.12      (![X0 : $i, X1 : $i]:
% 13.92/14.12         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 13.92/14.12          | ~ (v2_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 13.92/14.12          | (r2_hidden @ (k1_funct_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 13.92/14.12             (k2_relat_1 @ (k2_funct_1 @ X0)))
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_relat_1 @ X0))),
% 13.92/14.12      inference('simplify', [status(thm)], ['136'])).
% 13.92/14.12  thf('138', plain,
% 13.92/14.12      (![X0 : $i, X1 : $i]:
% 13.92/14.12         (~ (v1_relat_1 @ X0)
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_relat_1 @ X0)
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | (r2_hidden @ (k1_funct_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 13.92/14.12             (k2_relat_1 @ (k2_funct_1 @ X0)))
% 13.92/14.12          | ~ (v2_funct_1 @ X0)
% 13.92/14.12          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 13.92/14.12      inference('sup-', [status(thm)], ['131', '137'])).
% 13.92/14.12  thf('139', plain,
% 13.92/14.12      (![X0 : $i, X1 : $i]:
% 13.92/14.12         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 13.92/14.12          | ~ (v2_funct_1 @ X0)
% 13.92/14.12          | (r2_hidden @ (k1_funct_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 13.92/14.12             (k2_relat_1 @ (k2_funct_1 @ X0)))
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_relat_1 @ X0))),
% 13.92/14.12      inference('simplify', [status(thm)], ['138'])).
% 13.92/14.12  thf('140', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         (~ (r2_hidden @ X0 @ sk_B)
% 13.92/14.12          | ~ (v1_relat_1 @ sk_C_1)
% 13.92/14.12          | ~ (v1_funct_1 @ sk_C_1)
% 13.92/14.12          | (r2_hidden @ (k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ X0) @ 
% 13.92/14.12             (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 13.92/14.12          | ~ (v2_funct_1 @ sk_C_1))),
% 13.92/14.12      inference('sup-', [status(thm)], ['130', '139'])).
% 13.92/14.12  thf('141', plain, ((v1_relat_1 @ sk_C_1)),
% 13.92/14.12      inference('demod', [status(thm)], ['43', '44'])).
% 13.92/14.12  thf('142', plain, ((v1_funct_1 @ sk_C_1)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('143', plain, ((v2_funct_1 @ sk_C_1)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('144', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         (~ (r2_hidden @ X0 @ sk_B)
% 13.92/14.12          | (r2_hidden @ (k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ X0) @ 
% 13.92/14.12             (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 13.92/14.12      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 13.92/14.12  thf('145', plain,
% 13.92/14.12      (![X13 : $i]:
% 13.92/14.12         (~ (v2_funct_1 @ X13)
% 13.92/14.12          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 13.92/14.12          | ~ (v1_funct_1 @ X13)
% 13.92/14.12          | ~ (v1_relat_1 @ X13))),
% 13.92/14.12      inference('cnf', [status(esa)], [t55_funct_1])).
% 13.92/14.12  thf('146', plain,
% 13.92/14.12      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 13.92/14.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 13.92/14.12      inference('simplify', [status(thm)], ['74'])).
% 13.92/14.12  thf('147', plain,
% 13.92/14.12      (![X16 : $i, X17 : $i, X18 : $i]:
% 13.92/14.12         ((m1_subset_1 @ (k2_relset_1 @ X16 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 13.92/14.12          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 13.92/14.12      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 13.92/14.12  thf('148', plain,
% 13.92/14.12      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C_1)) @ 
% 13.92/14.12        (k1_zfmisc_1 @ sk_A))),
% 13.92/14.12      inference('sup-', [status(thm)], ['146', '147'])).
% 13.92/14.12  thf('149', plain,
% 13.92/14.12      (![X3 : $i, X4 : $i]:
% 13.92/14.12         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 13.92/14.12      inference('cnf', [status(esa)], [t3_subset])).
% 13.92/14.12  thf('150', plain,
% 13.92/14.12      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C_1)) @ sk_A)),
% 13.92/14.12      inference('sup-', [status(thm)], ['148', '149'])).
% 13.92/14.12  thf('151', plain,
% 13.92/14.12      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 13.92/14.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 13.92/14.12      inference('simplify', [status(thm)], ['74'])).
% 13.92/14.12  thf('152', plain,
% 13.92/14.12      (![X22 : $i, X23 : $i, X24 : $i]:
% 13.92/14.12         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 13.92/14.12          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 13.92/14.12      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 13.92/14.12  thf('153', plain,
% 13.92/14.12      (((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C_1))
% 13.92/14.12         = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 13.92/14.12      inference('sup-', [status(thm)], ['151', '152'])).
% 13.92/14.12  thf('154', plain,
% 13.92/14.12      ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_A)),
% 13.92/14.12      inference('demod', [status(thm)], ['150', '153'])).
% 13.92/14.12  thf('155', plain,
% 13.92/14.12      (![X0 : $i, X2 : $i]:
% 13.92/14.12         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 13.92/14.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.92/14.12  thf('156', plain,
% 13.92/14.12      ((~ (r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 13.92/14.12        | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 13.92/14.12      inference('sup-', [status(thm)], ['154', '155'])).
% 13.92/14.12  thf('157', plain,
% 13.92/14.12      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C_1))
% 13.92/14.12        | ~ (v1_relat_1 @ sk_C_1)
% 13.92/14.12        | ~ (v1_funct_1 @ sk_C_1)
% 13.92/14.12        | ~ (v2_funct_1 @ sk_C_1)
% 13.92/14.12        | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 13.92/14.12      inference('sup-', [status(thm)], ['145', '156'])).
% 13.92/14.12  thf('158', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 13.92/14.12      inference('demod', [status(thm)], ['2', '9', '12'])).
% 13.92/14.12  thf('159', plain,
% 13.92/14.12      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 13.92/14.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.92/14.12  thf('160', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 13.92/14.12      inference('simplify', [status(thm)], ['159'])).
% 13.92/14.12  thf('161', plain, ((v1_relat_1 @ sk_C_1)),
% 13.92/14.12      inference('demod', [status(thm)], ['43', '44'])).
% 13.92/14.12  thf('162', plain, ((v1_funct_1 @ sk_C_1)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('163', plain, ((v2_funct_1 @ sk_C_1)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('164', plain, (((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 13.92/14.12      inference('demod', [status(thm)],
% 13.92/14.12                ['157', '158', '160', '161', '162', '163'])).
% 13.92/14.12  thf('165', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         (~ (r2_hidden @ X0 @ sk_B)
% 13.92/14.12          | (r2_hidden @ (k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ X0) @ sk_A))),
% 13.92/14.12      inference('demod', [status(thm)], ['144', '164'])).
% 13.92/14.12  thf('166', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         ((zip_tseitin_3 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)
% 13.92/14.12          | (r2_hidden @ 
% 13.92/14.12             (k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ 
% 13.92/14.12              (sk_D_1 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)) @ 
% 13.92/14.12             sk_A))),
% 13.92/14.12      inference('sup-', [status(thm)], ['129', '165'])).
% 13.92/14.12  thf('167', plain,
% 13.92/14.12      (![X48 : $i, X49 : $i]:
% 13.92/14.12         (((k1_funct_1 @ sk_D_2 @ X48) = (X49))
% 13.92/14.12          | ((k1_funct_1 @ sk_C_1 @ X49) != (X48))
% 13.92/14.12          | ~ (r2_hidden @ X49 @ sk_A))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('168', plain,
% 13.92/14.12      (![X49 : $i]:
% 13.92/14.12         (~ (r2_hidden @ X49 @ sk_A)
% 13.92/14.12          | ((k1_funct_1 @ sk_D_2 @ (k1_funct_1 @ sk_C_1 @ X49)) = (X49)))),
% 13.92/14.12      inference('simplify', [status(thm)], ['167'])).
% 13.92/14.12  thf('169', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         ((zip_tseitin_3 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)
% 13.92/14.12          | ((k1_funct_1 @ sk_D_2 @ 
% 13.92/14.12              (k1_funct_1 @ sk_C_1 @ 
% 13.92/14.12               (k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ 
% 13.92/14.12                (sk_D_1 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B))))
% 13.92/14.12              = (k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ 
% 13.92/14.12                 (sk_D_1 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B))))),
% 13.92/14.12      inference('sup-', [status(thm)], ['166', '168'])).
% 13.92/14.12  thf('170', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         ((zip_tseitin_3 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)
% 13.92/14.12          | (r2_hidden @ 
% 13.92/14.12             (k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ 
% 13.92/14.12              (sk_D_1 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)) @ 
% 13.92/14.12             sk_A))),
% 13.92/14.12      inference('sup-', [status(thm)], ['129', '165'])).
% 13.92/14.12  thf('171', plain,
% 13.92/14.12      (![X48 : $i, X49 : $i]:
% 13.92/14.12         ((r2_hidden @ X48 @ sk_B)
% 13.92/14.12          | ((k1_funct_1 @ sk_C_1 @ X49) != (X48))
% 13.92/14.12          | ~ (r2_hidden @ X49 @ sk_A))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('172', plain,
% 13.92/14.12      (![X49 : $i]:
% 13.92/14.12         (~ (r2_hidden @ X49 @ sk_A)
% 13.92/14.12          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X49) @ sk_B))),
% 13.92/14.12      inference('simplify', [status(thm)], ['171'])).
% 13.92/14.12  thf('173', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         ((zip_tseitin_3 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)
% 13.92/14.12          | (r2_hidden @ 
% 13.92/14.12             (k1_funct_1 @ sk_C_1 @ 
% 13.92/14.12              (k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ 
% 13.92/14.12               (sk_D_1 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B))) @ 
% 13.92/14.12             sk_B))),
% 13.92/14.12      inference('sup-', [status(thm)], ['170', '172'])).
% 13.92/14.12  thf('174', plain, (((sk_B) = (k1_relat_1 @ sk_D_2))),
% 13.92/14.12      inference('demod', [status(thm)], ['16', '23', '26'])).
% 13.92/14.12  thf('175', plain,
% 13.92/14.12      (![X11 : $i, X12 : $i]:
% 13.92/14.12         (~ (r2_hidden @ X11 @ (k1_relat_1 @ X12))
% 13.92/14.12          | (r2_hidden @ (k1_funct_1 @ X12 @ X11) @ (k2_relat_1 @ X12))
% 13.92/14.12          | ~ (v1_funct_1 @ X12)
% 13.92/14.12          | ~ (v1_relat_1 @ X12))),
% 13.92/14.12      inference('cnf', [status(esa)], [t12_funct_1])).
% 13.92/14.12  thf('176', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         (~ (r2_hidden @ X0 @ sk_B)
% 13.92/14.12          | ~ (v1_relat_1 @ sk_D_2)
% 13.92/14.12          | ~ (v1_funct_1 @ sk_D_2)
% 13.92/14.12          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 13.92/14.12      inference('sup-', [status(thm)], ['174', '175'])).
% 13.92/14.12  thf('177', plain, ((v1_relat_1 @ sk_D_2)),
% 13.92/14.12      inference('demod', [status(thm)], ['34', '35'])).
% 13.92/14.12  thf('178', plain, ((v1_funct_1 @ sk_D_2)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('179', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         (~ (r2_hidden @ X0 @ sk_B)
% 13.92/14.12          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 13.92/14.12      inference('demod', [status(thm)], ['176', '177', '178'])).
% 13.92/14.12  thf('180', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         ((zip_tseitin_3 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)
% 13.92/14.12          | (r2_hidden @ 
% 13.92/14.12             (k1_funct_1 @ sk_D_2 @ 
% 13.92/14.12              (k1_funct_1 @ sk_C_1 @ 
% 13.92/14.12               (k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ 
% 13.92/14.12                (sk_D_1 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)))) @ 
% 13.92/14.12             (k2_relat_1 @ sk_D_2)))),
% 13.92/14.12      inference('sup-', [status(thm)], ['173', '179'])).
% 13.92/14.12  thf('181', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         ((r2_hidden @ 
% 13.92/14.12           (k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ 
% 13.92/14.12            (sk_D_1 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)) @ 
% 13.92/14.12           (k2_relat_1 @ sk_D_2))
% 13.92/14.12          | (zip_tseitin_3 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)
% 13.92/14.12          | (zip_tseitin_3 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B))),
% 13.92/14.12      inference('sup+', [status(thm)], ['169', '180'])).
% 13.92/14.12  thf('182', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         ((zip_tseitin_3 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)
% 13.92/14.12          | (r2_hidden @ 
% 13.92/14.12             (k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ 
% 13.92/14.12              (sk_D_1 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)) @ 
% 13.92/14.12             (k2_relat_1 @ sk_D_2)))),
% 13.92/14.12      inference('simplify', [status(thm)], ['181'])).
% 13.92/14.12  thf('183', plain,
% 13.92/14.12      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 13.92/14.12         ((zip_tseitin_2 @ X37 @ X38 @ X39 @ X40)
% 13.92/14.12          | ~ (r2_hidden @ (k1_funct_1 @ X38 @ X37) @ X39))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_6])).
% 13.92/14.12  thf('184', plain,
% 13.92/14.12      (![X0 : $i, X1 : $i]:
% 13.92/14.12         ((zip_tseitin_3 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)
% 13.92/14.12          | (zip_tseitin_2 @ (sk_D_1 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B) @ 
% 13.92/14.12             (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_D_2) @ X1))),
% 13.92/14.12      inference('sup-', [status(thm)], ['182', '183'])).
% 13.92/14.12  thf('185', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         (~ (zip_tseitin_2 @ (sk_D_1 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B) @ 
% 13.92/14.12             (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)
% 13.92/14.12          | (zip_tseitin_3 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B))),
% 13.92/14.12      inference('demod', [status(thm)], ['111', '112', '113', '122', '127'])).
% 13.92/14.12  thf('186', plain,
% 13.92/14.12      (((zip_tseitin_3 @ (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_D_2) @ sk_B)
% 13.92/14.12        | (zip_tseitin_3 @ (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_D_2) @ sk_B))),
% 13.92/14.12      inference('sup-', [status(thm)], ['184', '185'])).
% 13.92/14.12  thf('187', plain,
% 13.92/14.12      ((zip_tseitin_3 @ (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_D_2) @ sk_B)),
% 13.92/14.12      inference('simplify', [status(thm)], ['186'])).
% 13.92/14.12  thf('188', plain,
% 13.92/14.12      (![X41 : $i, X42 : $i, X43 : $i]:
% 13.92/14.12         ((m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 13.92/14.12          | ~ (zip_tseitin_3 @ X41 @ X42 @ X43))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_8])).
% 13.92/14.12  thf('189', plain,
% 13.92/14.12      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 13.92/14.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_D_2))))),
% 13.92/14.12      inference('sup-', [status(thm)], ['187', '188'])).
% 13.92/14.12  thf('190', plain,
% 13.92/14.12      (![X16 : $i, X17 : $i, X18 : $i]:
% 13.92/14.12         ((m1_subset_1 @ (k2_relset_1 @ X16 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 13.92/14.12          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 13.92/14.12      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 13.92/14.12  thf('191', plain,
% 13.92/14.12      ((m1_subset_1 @ 
% 13.92/14.12        (k2_relset_1 @ sk_B @ (k2_relat_1 @ sk_D_2) @ (k2_funct_1 @ sk_C_1)) @ 
% 13.92/14.12        (k1_zfmisc_1 @ (k2_relat_1 @ sk_D_2)))),
% 13.92/14.12      inference('sup-', [status(thm)], ['189', '190'])).
% 13.92/14.12  thf('192', plain,
% 13.92/14.12      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 13.92/14.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_D_2))))),
% 13.92/14.12      inference('sup-', [status(thm)], ['187', '188'])).
% 13.92/14.12  thf('193', plain,
% 13.92/14.12      (![X22 : $i, X23 : $i, X24 : $i]:
% 13.92/14.12         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 13.92/14.12          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 13.92/14.12      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 13.92/14.12  thf('194', plain,
% 13.92/14.12      (((k2_relset_1 @ sk_B @ (k2_relat_1 @ sk_D_2) @ (k2_funct_1 @ sk_C_1))
% 13.92/14.12         = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 13.92/14.12      inference('sup-', [status(thm)], ['192', '193'])).
% 13.92/14.12  thf('195', plain, (((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 13.92/14.12      inference('demod', [status(thm)],
% 13.92/14.12                ['157', '158', '160', '161', '162', '163'])).
% 13.92/14.12  thf('196', plain,
% 13.92/14.12      (((k2_relset_1 @ sk_B @ (k2_relat_1 @ sk_D_2) @ (k2_funct_1 @ sk_C_1))
% 13.92/14.12         = (sk_A))),
% 13.92/14.12      inference('demod', [status(thm)], ['194', '195'])).
% 13.92/14.12  thf('197', plain,
% 13.92/14.12      ((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ (k2_relat_1 @ sk_D_2)))),
% 13.92/14.12      inference('demod', [status(thm)], ['191', '196'])).
% 13.92/14.12  thf('198', plain,
% 13.92/14.12      (![X3 : $i, X4 : $i]:
% 13.92/14.12         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 13.92/14.12      inference('cnf', [status(esa)], [t3_subset])).
% 13.92/14.12  thf('199', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 13.92/14.12      inference('sup-', [status(thm)], ['197', '198'])).
% 13.92/14.12  thf('200', plain, (((sk_A) = (k2_relat_1 @ sk_D_2))),
% 13.92/14.12      inference('demod', [status(thm)], ['65', '199'])).
% 13.92/14.12  thf('201', plain,
% 13.92/14.12      (((r2_hidden @ (sk_D @ sk_D_2 @ sk_C_1) @ sk_B) | ((sk_A) != (sk_A)))),
% 13.92/14.12      inference('demod', [status(thm)], ['54', '200'])).
% 13.92/14.12  thf('202', plain, ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C_1) @ sk_B)),
% 13.92/14.12      inference('simplify', [status(thm)], ['201'])).
% 13.92/14.12  thf('203', plain,
% 13.92/14.12      (![X47 : $i, X48 : $i]:
% 13.92/14.12         (((k1_funct_1 @ sk_C_1 @ X47) = (X48))
% 13.92/14.12          | ((k1_funct_1 @ sk_D_2 @ X48) != (X47))
% 13.92/14.12          | ~ (r2_hidden @ X48 @ sk_B))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('204', plain,
% 13.92/14.12      (![X48 : $i]:
% 13.92/14.12         (~ (r2_hidden @ X48 @ sk_B)
% 13.92/14.12          | ((k1_funct_1 @ sk_C_1 @ (k1_funct_1 @ sk_D_2 @ X48)) = (X48)))),
% 13.92/14.12      inference('simplify', [status(thm)], ['203'])).
% 13.92/14.12  thf('205', plain,
% 13.92/14.12      (((k1_funct_1 @ sk_C_1 @ (k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C_1)))
% 13.92/14.12         = (sk_D @ sk_D_2 @ sk_C_1))),
% 13.92/14.12      inference('sup-', [status(thm)], ['202', '204'])).
% 13.92/14.12  thf('206', plain, (((sk_B) = (k1_relat_1 @ sk_D_2))),
% 13.92/14.12      inference('demod', [status(thm)], ['16', '23', '26'])).
% 13.92/14.12  thf('207', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 13.92/14.12      inference('sup+', [status(thm)], ['48', '49'])).
% 13.92/14.12  thf('208', plain,
% 13.92/14.12      (![X14 : $i, X15 : $i]:
% 13.92/14.12         (~ (v1_relat_1 @ X14)
% 13.92/14.12          | ~ (v1_funct_1 @ X14)
% 13.92/14.12          | ((X14) = (k2_funct_1 @ X15))
% 13.92/14.12          | ((k1_funct_1 @ X15 @ (sk_C @ X14 @ X15)) = (sk_D @ X14 @ X15))
% 13.92/14.12          | ((k1_funct_1 @ X14 @ (sk_D @ X14 @ X15)) = (sk_C @ X14 @ X15))
% 13.92/14.12          | ((k2_relat_1 @ X15) != (k1_relat_1 @ X14))
% 13.92/14.12          | ((k1_relat_1 @ X15) != (k2_relat_1 @ X14))
% 13.92/14.12          | ~ (v2_funct_1 @ X15)
% 13.92/14.12          | ~ (v1_funct_1 @ X15)
% 13.92/14.12          | ~ (v1_relat_1 @ X15))),
% 13.92/14.12      inference('cnf', [status(esa)], [t60_funct_1])).
% 13.92/14.12  thf('209', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         (((sk_B) != (k1_relat_1 @ X0))
% 13.92/14.12          | ~ (v1_relat_1 @ sk_C_1)
% 13.92/14.12          | ~ (v1_funct_1 @ sk_C_1)
% 13.92/14.12          | ~ (v2_funct_1 @ sk_C_1)
% 13.92/14.12          | ((k1_relat_1 @ sk_C_1) != (k2_relat_1 @ X0))
% 13.92/14.12          | ((k1_funct_1 @ X0 @ (sk_D @ X0 @ sk_C_1)) = (sk_C @ X0 @ sk_C_1))
% 13.92/14.12          | ((k1_funct_1 @ sk_C_1 @ (sk_C @ X0 @ sk_C_1))
% 13.92/14.12              = (sk_D @ X0 @ sk_C_1))
% 13.92/14.12          | ((X0) = (k2_funct_1 @ sk_C_1))
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_relat_1 @ X0))),
% 13.92/14.12      inference('sup-', [status(thm)], ['207', '208'])).
% 13.92/14.12  thf('210', plain, ((v1_relat_1 @ sk_C_1)),
% 13.92/14.12      inference('demod', [status(thm)], ['43', '44'])).
% 13.92/14.12  thf('211', plain, ((v1_funct_1 @ sk_C_1)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('212', plain, ((v2_funct_1 @ sk_C_1)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('213', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         (((sk_B) != (k1_relat_1 @ X0))
% 13.92/14.12          | ((k1_relat_1 @ sk_C_1) != (k2_relat_1 @ X0))
% 13.92/14.12          | ((k1_funct_1 @ X0 @ (sk_D @ X0 @ sk_C_1)) = (sk_C @ X0 @ sk_C_1))
% 13.92/14.12          | ((k1_funct_1 @ sk_C_1 @ (sk_C @ X0 @ sk_C_1))
% 13.92/14.12              = (sk_D @ X0 @ sk_C_1))
% 13.92/14.12          | ((X0) = (k2_funct_1 @ sk_C_1))
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_relat_1 @ X0))),
% 13.92/14.12      inference('demod', [status(thm)], ['209', '210', '211', '212'])).
% 13.92/14.12  thf('214', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 13.92/14.12      inference('demod', [status(thm)], ['2', '9', '12'])).
% 13.92/14.12  thf('215', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         (((sk_B) != (k1_relat_1 @ X0))
% 13.92/14.12          | ((sk_A) != (k2_relat_1 @ X0))
% 13.92/14.12          | ((k1_funct_1 @ X0 @ (sk_D @ X0 @ sk_C_1)) = (sk_C @ X0 @ sk_C_1))
% 13.92/14.12          | ((k1_funct_1 @ sk_C_1 @ (sk_C @ X0 @ sk_C_1))
% 13.92/14.12              = (sk_D @ X0 @ sk_C_1))
% 13.92/14.12          | ((X0) = (k2_funct_1 @ sk_C_1))
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_relat_1 @ X0))),
% 13.92/14.12      inference('demod', [status(thm)], ['213', '214'])).
% 13.92/14.12  thf('216', plain,
% 13.92/14.12      ((((sk_B) != (sk_B))
% 13.92/14.12        | ~ (v1_relat_1 @ sk_D_2)
% 13.92/14.12        | ~ (v1_funct_1 @ sk_D_2)
% 13.92/14.12        | ((sk_D_2) = (k2_funct_1 @ sk_C_1))
% 13.92/14.12        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D_2 @ sk_C_1))
% 13.92/14.12            = (sk_D @ sk_D_2 @ sk_C_1))
% 13.92/14.12        | ((k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C_1))
% 13.92/14.12            = (sk_C @ sk_D_2 @ sk_C_1))
% 13.92/14.12        | ((sk_A) != (k2_relat_1 @ sk_D_2)))),
% 13.92/14.12      inference('sup-', [status(thm)], ['206', '215'])).
% 13.92/14.12  thf('217', plain, ((v1_relat_1 @ sk_D_2)),
% 13.92/14.12      inference('demod', [status(thm)], ['34', '35'])).
% 13.92/14.12  thf('218', plain, ((v1_funct_1 @ sk_D_2)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('219', plain,
% 13.92/14.12      ((((sk_B) != (sk_B))
% 13.92/14.12        | ((sk_D_2) = (k2_funct_1 @ sk_C_1))
% 13.92/14.12        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D_2 @ sk_C_1))
% 13.92/14.12            = (sk_D @ sk_D_2 @ sk_C_1))
% 13.92/14.12        | ((k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C_1))
% 13.92/14.12            = (sk_C @ sk_D_2 @ sk_C_1))
% 13.92/14.12        | ((sk_A) != (k2_relat_1 @ sk_D_2)))),
% 13.92/14.12      inference('demod', [status(thm)], ['216', '217', '218'])).
% 13.92/14.12  thf('220', plain,
% 13.92/14.12      ((((sk_A) != (k2_relat_1 @ sk_D_2))
% 13.92/14.12        | ((k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C_1))
% 13.92/14.12            = (sk_C @ sk_D_2 @ sk_C_1))
% 13.92/14.12        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D_2 @ sk_C_1))
% 13.92/14.12            = (sk_D @ sk_D_2 @ sk_C_1))
% 13.92/14.12        | ((sk_D_2) = (k2_funct_1 @ sk_C_1)))),
% 13.92/14.12      inference('simplify', [status(thm)], ['219'])).
% 13.92/14.12  thf('221', plain, (((sk_D_2) != (k2_funct_1 @ sk_C_1))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('222', plain,
% 13.92/14.12      ((((sk_A) != (k2_relat_1 @ sk_D_2))
% 13.92/14.12        | ((k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C_1))
% 13.92/14.12            = (sk_C @ sk_D_2 @ sk_C_1))
% 13.92/14.12        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D_2 @ sk_C_1))
% 13.92/14.12            = (sk_D @ sk_D_2 @ sk_C_1)))),
% 13.92/14.12      inference('simplify_reflect-', [status(thm)], ['220', '221'])).
% 13.92/14.12  thf('223', plain, (((sk_A) = (k2_relat_1 @ sk_D_2))),
% 13.92/14.12      inference('demod', [status(thm)], ['65', '199'])).
% 13.92/14.12  thf('224', plain,
% 13.92/14.12      ((((sk_A) != (sk_A))
% 13.92/14.12        | ((k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C_1))
% 13.92/14.12            = (sk_C @ sk_D_2 @ sk_C_1))
% 13.92/14.12        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D_2 @ sk_C_1))
% 13.92/14.12            = (sk_D @ sk_D_2 @ sk_C_1)))),
% 13.92/14.12      inference('demod', [status(thm)], ['222', '223'])).
% 13.92/14.12  thf('225', plain,
% 13.92/14.12      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D_2 @ sk_C_1))
% 13.92/14.12          = (sk_D @ sk_D_2 @ sk_C_1))
% 13.92/14.12        | ((k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C_1))
% 13.92/14.12            = (sk_C @ sk_D_2 @ sk_C_1)))),
% 13.92/14.12      inference('simplify', [status(thm)], ['224'])).
% 13.92/14.12  thf('226', plain, (((sk_B) = (k1_relat_1 @ sk_D_2))),
% 13.92/14.12      inference('demod', [status(thm)], ['16', '23', '26'])).
% 13.92/14.12  thf('227', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 13.92/14.12      inference('sup+', [status(thm)], ['48', '49'])).
% 13.92/14.12  thf('228', plain,
% 13.92/14.12      (![X14 : $i, X15 : $i]:
% 13.92/14.12         (~ (v1_relat_1 @ X14)
% 13.92/14.12          | ~ (v1_funct_1 @ X14)
% 13.92/14.12          | ((X14) = (k2_funct_1 @ X15))
% 13.92/14.12          | (r2_hidden @ (sk_C @ X14 @ X15) @ (k1_relat_1 @ X15))
% 13.92/14.12          | ((k2_relat_1 @ X15) != (k1_relat_1 @ X14))
% 13.92/14.12          | ((k1_relat_1 @ X15) != (k2_relat_1 @ X14))
% 13.92/14.12          | ~ (v2_funct_1 @ X15)
% 13.92/14.12          | ~ (v1_funct_1 @ X15)
% 13.92/14.12          | ~ (v1_relat_1 @ X15))),
% 13.92/14.12      inference('cnf', [status(esa)], [t60_funct_1])).
% 13.92/14.12  thf('229', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         (((sk_B) != (k1_relat_1 @ X0))
% 13.92/14.12          | ~ (v1_relat_1 @ sk_C_1)
% 13.92/14.12          | ~ (v1_funct_1 @ sk_C_1)
% 13.92/14.12          | ~ (v2_funct_1 @ sk_C_1)
% 13.92/14.12          | ((k1_relat_1 @ sk_C_1) != (k2_relat_1 @ X0))
% 13.92/14.12          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 13.92/14.12          | ((X0) = (k2_funct_1 @ sk_C_1))
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_relat_1 @ X0))),
% 13.92/14.12      inference('sup-', [status(thm)], ['227', '228'])).
% 13.92/14.12  thf('230', plain, ((v1_relat_1 @ sk_C_1)),
% 13.92/14.12      inference('demod', [status(thm)], ['43', '44'])).
% 13.92/14.12  thf('231', plain, ((v1_funct_1 @ sk_C_1)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('232', plain, ((v2_funct_1 @ sk_C_1)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('233', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 13.92/14.12      inference('demod', [status(thm)], ['2', '9', '12'])).
% 13.92/14.12  thf('234', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 13.92/14.12      inference('demod', [status(thm)], ['2', '9', '12'])).
% 13.92/14.12  thf('235', plain,
% 13.92/14.12      (![X0 : $i]:
% 13.92/14.12         (((sk_B) != (k1_relat_1 @ X0))
% 13.92/14.12          | ((sk_A) != (k2_relat_1 @ X0))
% 13.92/14.12          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 13.92/14.12          | ((X0) = (k2_funct_1 @ sk_C_1))
% 13.92/14.12          | ~ (v1_funct_1 @ X0)
% 13.92/14.12          | ~ (v1_relat_1 @ X0))),
% 13.92/14.12      inference('demod', [status(thm)],
% 13.92/14.12                ['229', '230', '231', '232', '233', '234'])).
% 13.92/14.12  thf('236', plain,
% 13.92/14.12      ((((sk_B) != (sk_B))
% 13.92/14.12        | ~ (v1_relat_1 @ sk_D_2)
% 13.92/14.12        | ~ (v1_funct_1 @ sk_D_2)
% 13.92/14.12        | ((sk_D_2) = (k2_funct_1 @ sk_C_1))
% 13.92/14.12        | (r2_hidden @ (sk_C @ sk_D_2 @ sk_C_1) @ sk_A)
% 13.92/14.12        | ((sk_A) != (k2_relat_1 @ sk_D_2)))),
% 13.92/14.12      inference('sup-', [status(thm)], ['226', '235'])).
% 13.92/14.12  thf('237', plain, ((v1_relat_1 @ sk_D_2)),
% 13.92/14.12      inference('demod', [status(thm)], ['34', '35'])).
% 13.92/14.12  thf('238', plain, ((v1_funct_1 @ sk_D_2)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('239', plain,
% 13.92/14.12      ((((sk_B) != (sk_B))
% 13.92/14.12        | ((sk_D_2) = (k2_funct_1 @ sk_C_1))
% 13.92/14.12        | (r2_hidden @ (sk_C @ sk_D_2 @ sk_C_1) @ sk_A)
% 13.92/14.12        | ((sk_A) != (k2_relat_1 @ sk_D_2)))),
% 13.92/14.12      inference('demod', [status(thm)], ['236', '237', '238'])).
% 13.92/14.12  thf('240', plain,
% 13.92/14.12      ((((sk_A) != (k2_relat_1 @ sk_D_2))
% 13.92/14.12        | (r2_hidden @ (sk_C @ sk_D_2 @ sk_C_1) @ sk_A)
% 13.92/14.12        | ((sk_D_2) = (k2_funct_1 @ sk_C_1)))),
% 13.92/14.12      inference('simplify', [status(thm)], ['239'])).
% 13.92/14.12  thf('241', plain, (((sk_D_2) != (k2_funct_1 @ sk_C_1))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('242', plain,
% 13.92/14.12      ((((sk_A) != (k2_relat_1 @ sk_D_2))
% 13.92/14.12        | (r2_hidden @ (sk_C @ sk_D_2 @ sk_C_1) @ sk_A))),
% 13.92/14.12      inference('simplify_reflect-', [status(thm)], ['240', '241'])).
% 13.92/14.12  thf('243', plain, (((sk_A) = (k2_relat_1 @ sk_D_2))),
% 13.92/14.12      inference('demod', [status(thm)], ['65', '199'])).
% 13.92/14.12  thf('244', plain,
% 13.92/14.12      ((((sk_A) != (sk_A)) | (r2_hidden @ (sk_C @ sk_D_2 @ sk_C_1) @ sk_A))),
% 13.92/14.12      inference('demod', [status(thm)], ['242', '243'])).
% 13.92/14.12  thf('245', plain, ((r2_hidden @ (sk_C @ sk_D_2 @ sk_C_1) @ sk_A)),
% 13.92/14.12      inference('simplify', [status(thm)], ['244'])).
% 13.92/14.12  thf('246', plain,
% 13.92/14.12      (![X49 : $i]:
% 13.92/14.12         (~ (r2_hidden @ X49 @ sk_A)
% 13.92/14.12          | ((k1_funct_1 @ sk_D_2 @ (k1_funct_1 @ sk_C_1 @ X49)) = (X49)))),
% 13.92/14.12      inference('simplify', [status(thm)], ['167'])).
% 13.92/14.12  thf('247', plain,
% 13.92/14.12      (((k1_funct_1 @ sk_D_2 @ (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D_2 @ sk_C_1)))
% 13.92/14.12         = (sk_C @ sk_D_2 @ sk_C_1))),
% 13.92/14.12      inference('sup-', [status(thm)], ['245', '246'])).
% 13.92/14.12  thf('248', plain,
% 13.92/14.12      ((((k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C_1))
% 13.92/14.12          = (sk_C @ sk_D_2 @ sk_C_1))
% 13.92/14.12        | ((k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C_1))
% 13.92/14.12            = (sk_C @ sk_D_2 @ sk_C_1)))),
% 13.92/14.12      inference('sup+', [status(thm)], ['225', '247'])).
% 13.92/14.12  thf('249', plain,
% 13.92/14.12      (((k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C_1))
% 13.92/14.12         = (sk_C @ sk_D_2 @ sk_C_1))),
% 13.92/14.12      inference('simplify', [status(thm)], ['248'])).
% 13.92/14.12  thf('250', plain,
% 13.92/14.12      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D_2 @ sk_C_1))
% 13.92/14.12         = (sk_D @ sk_D_2 @ sk_C_1))),
% 13.92/14.12      inference('demod', [status(thm)], ['205', '249'])).
% 13.92/14.12  thf('251', plain,
% 13.92/14.12      (![X14 : $i, X15 : $i]:
% 13.92/14.12         (~ (v1_relat_1 @ X14)
% 13.92/14.12          | ~ (v1_funct_1 @ X14)
% 13.92/14.12          | ((X14) = (k2_funct_1 @ X15))
% 13.92/14.12          | ((k1_funct_1 @ X15 @ (sk_C @ X14 @ X15)) != (sk_D @ X14 @ X15))
% 13.92/14.12          | ((k1_funct_1 @ X14 @ (sk_D @ X14 @ X15)) != (sk_C @ X14 @ X15))
% 13.92/14.12          | ((k2_relat_1 @ X15) != (k1_relat_1 @ X14))
% 13.92/14.12          | ((k1_relat_1 @ X15) != (k2_relat_1 @ X14))
% 13.92/14.12          | ~ (v2_funct_1 @ X15)
% 13.92/14.12          | ~ (v1_funct_1 @ X15)
% 13.92/14.12          | ~ (v1_relat_1 @ X15))),
% 13.92/14.12      inference('cnf', [status(esa)], [t60_funct_1])).
% 13.92/14.12  thf('252', plain,
% 13.92/14.12      ((((sk_D @ sk_D_2 @ sk_C_1) != (sk_D @ sk_D_2 @ sk_C_1))
% 13.92/14.12        | ~ (v1_relat_1 @ sk_C_1)
% 13.92/14.12        | ~ (v1_funct_1 @ sk_C_1)
% 13.92/14.12        | ~ (v2_funct_1 @ sk_C_1)
% 13.92/14.12        | ((k1_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_D_2))
% 13.92/14.12        | ((k2_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D_2))
% 13.92/14.12        | ((k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C_1))
% 13.92/14.12            != (sk_C @ sk_D_2 @ sk_C_1))
% 13.92/14.12        | ((sk_D_2) = (k2_funct_1 @ sk_C_1))
% 13.92/14.12        | ~ (v1_funct_1 @ sk_D_2)
% 13.92/14.12        | ~ (v1_relat_1 @ sk_D_2))),
% 13.92/14.12      inference('sup-', [status(thm)], ['250', '251'])).
% 13.92/14.12  thf('253', plain, ((v1_relat_1 @ sk_C_1)),
% 13.92/14.12      inference('demod', [status(thm)], ['43', '44'])).
% 13.92/14.12  thf('254', plain, ((v1_funct_1 @ sk_C_1)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('255', plain, ((v2_funct_1 @ sk_C_1)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('256', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 13.92/14.12      inference('demod', [status(thm)], ['2', '9', '12'])).
% 13.92/14.12  thf('257', plain, (((sk_A) = (k2_relat_1 @ sk_D_2))),
% 13.92/14.12      inference('demod', [status(thm)], ['65', '199'])).
% 13.92/14.12  thf('258', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 13.92/14.12      inference('sup+', [status(thm)], ['48', '49'])).
% 13.92/14.12  thf('259', plain, (((sk_B) = (k1_relat_1 @ sk_D_2))),
% 13.92/14.12      inference('demod', [status(thm)], ['16', '23', '26'])).
% 13.92/14.12  thf('260', plain,
% 13.92/14.12      (((k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C_1))
% 13.92/14.12         = (sk_C @ sk_D_2 @ sk_C_1))),
% 13.92/14.12      inference('simplify', [status(thm)], ['248'])).
% 13.92/14.12  thf('261', plain, ((v1_funct_1 @ sk_D_2)),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('262', plain, ((v1_relat_1 @ sk_D_2)),
% 13.92/14.12      inference('demod', [status(thm)], ['34', '35'])).
% 13.92/14.12  thf('263', plain,
% 13.92/14.12      ((((sk_D @ sk_D_2 @ sk_C_1) != (sk_D @ sk_D_2 @ sk_C_1))
% 13.92/14.12        | ((sk_A) != (sk_A))
% 13.92/14.12        | ((sk_B) != (sk_B))
% 13.92/14.12        | ((sk_C @ sk_D_2 @ sk_C_1) != (sk_C @ sk_D_2 @ sk_C_1))
% 13.92/14.12        | ((sk_D_2) = (k2_funct_1 @ sk_C_1)))),
% 13.92/14.12      inference('demod', [status(thm)],
% 13.92/14.12                ['252', '253', '254', '255', '256', '257', '258', '259', 
% 13.92/14.12                 '260', '261', '262'])).
% 13.92/14.12  thf('264', plain, (((sk_D_2) = (k2_funct_1 @ sk_C_1))),
% 13.92/14.12      inference('simplify', [status(thm)], ['263'])).
% 13.92/14.12  thf('265', plain, (((sk_D_2) != (k2_funct_1 @ sk_C_1))),
% 13.92/14.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.92/14.12  thf('266', plain, ($false),
% 13.92/14.12      inference('simplify_reflect-', [status(thm)], ['264', '265'])).
% 13.92/14.12  
% 13.92/14.12  % SZS output end Refutation
% 13.92/14.12  
% 13.92/14.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
