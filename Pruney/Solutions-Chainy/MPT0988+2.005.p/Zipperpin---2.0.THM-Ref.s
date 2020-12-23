%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kHKazMYMda

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:52 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 625 expanded)
%              Number of leaves         :   34 ( 201 expanded)
%              Depth                    :   21
%              Number of atoms          : 1265 (20789 expanded)
%              Number of equality atoms :  105 (2089 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('2',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X21 ) @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('19',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['18'])).

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

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ( X15
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['7'])).

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

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 )
      | ( zip_tseitin_1 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('29',plain,
    ( sk_B
    = ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['21','28'])).

thf('30',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['10','29'])).

thf('31',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ( X15
        = ( k1_relset_1 @ X15 @ X16 @ X17 ) )
      | ~ ( zip_tseitin_1 @ X17 @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X19 )
      | ( zip_tseitin_1 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('37',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['33','40','43'])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('45',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( X6 = X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X6 ) @ ( k1_relat_1 @ X6 ) )
      | ( ( k1_relat_1 @ X6 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( sk_B
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_D ) @ ( k1_relat_1 @ sk_D ) )
      | ( sk_D = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('51',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['33','40','43'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_B
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_D ) @ sk_B )
      | ( sk_D = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','51','52','53'])).

thf('55',plain,
    ( ( sk_B != sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ sk_C_1 ) @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['30','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('60',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('63',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( sk_B != sk_B )
    | ( sk_D
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ sk_C_1 ) @ sk_D ) @ sk_B ) ),
    inference(demod,[status(thm)],['55','60','69'])).

thf('71',plain,
    ( ( r2_hidden @ ( sk_C @ ( k2_funct_1 @ sk_C_1 ) @ sk_D ) @ sk_B )
    | ( sk_D
      = ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    r2_hidden @ ( sk_C @ ( k2_funct_1 @ sk_C_1 ) @ sk_D ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r2_hidden @ X28 @ sk_A )
      | ( ( k1_funct_1 @ sk_D @ X29 )
       != X28 )
      | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X29: $i] :
      ( ~ ( r2_hidden @ X29 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X29 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ ( sk_C @ ( k2_funct_1 @ sk_C_1 ) @ sk_D ) ) @ sk_A ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ D )
          & ( r2_hidden @ C @ A ) )
       => ( ( B = k1_xboole_0 )
          | ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) )
            = C ) ) ) ) )).

thf('78',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ( X26 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X27 ) @ ( k1_funct_1 @ X27 @ X24 ) )
        = X24 )
      | ~ ( v2_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_C_1 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_funct_1 @ sk_C_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_funct_1 @ sk_C_1 @ X0 ) )
        = X0 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_funct_1 @ sk_C_1 @ X0 ) )
        = X0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_funct_1 @ sk_C_1 @ ( k1_funct_1 @ sk_D @ ( sk_C @ ( k2_funct_1 @ sk_C_1 ) @ sk_D ) ) ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ ( k2_funct_1 @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['76','85'])).

thf('87',plain,(
    r2_hidden @ ( sk_C @ ( k2_funct_1 @ sk_C_1 ) @ sk_D ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('88',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X28 )
        = X29 )
      | ( ( k1_funct_1 @ sk_D @ X29 )
       != X28 )
      | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X29: $i] :
      ( ~ ( r2_hidden @ X29 @ sk_B )
      | ( ( k1_funct_1 @ sk_C_1 @ ( k1_funct_1 @ sk_D @ X29 ) )
        = X29 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( k1_funct_1 @ sk_D @ ( sk_C @ ( k2_funct_1 @ sk_C_1 ) @ sk_D ) ) )
    = ( sk_C @ ( k2_funct_1 @ sk_C_1 ) @ sk_D ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,
    ( ( k1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( sk_C @ ( k2_funct_1 @ sk_C_1 ) @ sk_D ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ ( k2_funct_1 @ sk_C_1 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['86','90'])).

thf('92',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( X6 = X5 )
      | ( ( k1_funct_1 @ X6 @ ( sk_C @ X5 @ X6 ) )
       != ( k1_funct_1 @ X5 @ ( sk_C @ X5 @ X6 ) ) )
      | ( ( k1_relat_1 @ X6 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('93',plain,
    ( ( ( k1_funct_1 @ sk_D @ ( sk_C @ ( k2_funct_1 @ sk_C_1 ) @ sk_D ) )
     != ( k1_funct_1 @ sk_D @ ( sk_C @ ( k2_funct_1 @ sk_C_1 ) @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['49','50'])).

thf('95',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['33','40','43'])).

thf('97',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['10','29'])).

thf('98',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('99',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('100',plain,
    ( ( ( k1_funct_1 @ sk_D @ ( sk_C @ ( k2_funct_1 @ sk_C_1 ) @ sk_D ) )
     != ( k1_funct_1 @ sk_D @ ( sk_C @ ( k2_funct_1 @ sk_C_1 ) @ sk_D ) ) )
    | ( sk_B != sk_B )
    | ( sk_D
      = ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['93','94','95','96','97','98','99'])).

thf('101',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kHKazMYMda
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:26:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.44/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.71  % Solved by: fo/fo7.sh
% 0.44/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.71  % done 194 iterations in 0.227s
% 0.44/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.71  % SZS output start Refutation
% 0.44/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.44/0.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.44/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.71  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.44/0.71  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.44/0.71  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.44/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.71  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.44/0.71  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.44/0.71  thf(t34_funct_2, conjecture,
% 0.44/0.71    (![A:$i,B:$i,C:$i]:
% 0.44/0.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.71       ( ![D:$i]:
% 0.44/0.71         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.44/0.71             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.44/0.71           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) & 
% 0.44/0.71               ( ![E:$i,F:$i]:
% 0.44/0.71                 ( ( ( ( r2_hidden @ F @ A ) & 
% 0.44/0.71                       ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) =>
% 0.44/0.71                     ( ( r2_hidden @ E @ B ) & 
% 0.44/0.71                       ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) ) & 
% 0.44/0.71                   ( ( ( r2_hidden @ E @ B ) & 
% 0.44/0.71                       ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) =>
% 0.44/0.71                     ( ( r2_hidden @ F @ A ) & 
% 0.44/0.71                       ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) ) ) ) ) =>
% 0.44/0.71             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.44/0.71               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.44/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.71        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.71            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.71          ( ![D:$i]:
% 0.44/0.71            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.44/0.71                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.44/0.71              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.44/0.71                  ( v2_funct_1 @ C ) & 
% 0.44/0.71                  ( ![E:$i,F:$i]:
% 0.44/0.71                    ( ( ( ( r2_hidden @ F @ A ) & 
% 0.44/0.71                          ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) =>
% 0.44/0.71                        ( ( r2_hidden @ E @ B ) & 
% 0.44/0.71                          ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) ) & 
% 0.44/0.71                      ( ( ( r2_hidden @ E @ B ) & 
% 0.44/0.71                          ( ( k1_funct_1 @ D @ E ) = ( F ) ) ) =>
% 0.44/0.71                        ( ( r2_hidden @ F @ A ) & 
% 0.44/0.71                          ( ( k1_funct_1 @ C @ F ) = ( E ) ) ) ) ) ) ) =>
% 0.44/0.71                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.44/0.71                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.44/0.71    inference('cnf.neg', [status(esa)], [t34_funct_2])).
% 0.44/0.71  thf('0', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf(t31_funct_2, axiom,
% 0.44/0.71    (![A:$i,B:$i,C:$i]:
% 0.44/0.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.71       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.44/0.71         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.44/0.71           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.44/0.71           ( m1_subset_1 @
% 0.44/0.71             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.44/0.71  thf('1', plain,
% 0.44/0.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.71         (~ (v2_funct_1 @ X21)
% 0.44/0.71          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.44/0.71          | (m1_subset_1 @ (k2_funct_1 @ X21) @ 
% 0.44/0.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.44/0.71          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.44/0.71          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.44/0.71          | ~ (v1_funct_1 @ X21))),
% 0.44/0.71      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.44/0.71  thf('2', plain,
% 0.44/0.71      ((~ (v1_funct_1 @ sk_C_1)
% 0.44/0.71        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.44/0.71        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.44/0.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.44/0.71        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 0.44/0.71        | ~ (v2_funct_1 @ sk_C_1))),
% 0.44/0.71      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.71  thf('3', plain, ((v1_funct_1 @ sk_C_1)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('4', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('5', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('6', plain, ((v2_funct_1 @ sk_C_1)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('7', plain,
% 0.44/0.71      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.44/0.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.44/0.71        | ((sk_B) != (sk_B)))),
% 0.44/0.71      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.44/0.71  thf('8', plain,
% 0.44/0.71      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.44/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.44/0.71      inference('simplify', [status(thm)], ['7'])).
% 0.44/0.71  thf(redefinition_k1_relset_1, axiom,
% 0.44/0.71    (![A:$i,B:$i,C:$i]:
% 0.44/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.71       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.44/0.71  thf('9', plain,
% 0.44/0.71      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.71         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.44/0.71          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.44/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.44/0.71  thf('10', plain,
% 0.44/0.71      (((k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C_1))
% 0.44/0.71         = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.71  thf('11', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('12', plain,
% 0.44/0.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.71         (~ (v2_funct_1 @ X21)
% 0.44/0.71          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.44/0.71          | (v1_funct_2 @ (k2_funct_1 @ X21) @ X22 @ X23)
% 0.44/0.71          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.44/0.71          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.44/0.71          | ~ (v1_funct_1 @ X21))),
% 0.44/0.71      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.44/0.71  thf('13', plain,
% 0.44/0.71      ((~ (v1_funct_1 @ sk_C_1)
% 0.44/0.71        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.44/0.71        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)
% 0.44/0.71        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 0.44/0.71        | ~ (v2_funct_1 @ sk_C_1))),
% 0.44/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.71  thf('14', plain, ((v1_funct_1 @ sk_C_1)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('15', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('16', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('17', plain, ((v2_funct_1 @ sk_C_1)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('18', plain,
% 0.44/0.71      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.44/0.71      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.44/0.71  thf('19', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)),
% 0.44/0.71      inference('simplify', [status(thm)], ['18'])).
% 0.44/0.71  thf(d1_funct_2, axiom,
% 0.44/0.71    (![A:$i,B:$i,C:$i]:
% 0.44/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.71       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.71           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.44/0.71             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.44/0.71         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.71           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.44/0.71             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.44/0.71  thf(zf_stmt_1, axiom,
% 0.44/0.71    (![C:$i,B:$i,A:$i]:
% 0.44/0.71     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.44/0.71       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.44/0.71  thf('20', plain,
% 0.44/0.71      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.71         (~ (v1_funct_2 @ X17 @ X15 @ X16)
% 0.44/0.71          | ((X15) = (k1_relset_1 @ X15 @ X16 @ X17))
% 0.44/0.71          | ~ (zip_tseitin_1 @ X17 @ X16 @ X15))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.71  thf('21', plain,
% 0.44/0.71      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ sk_A @ sk_B)
% 0.44/0.71        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C_1))))),
% 0.44/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.44/0.71  thf(zf_stmt_2, axiom,
% 0.44/0.71    (![B:$i,A:$i]:
% 0.44/0.71     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.71       ( zip_tseitin_0 @ B @ A ) ))).
% 0.44/0.71  thf('22', plain,
% 0.44/0.71      (![X13 : $i, X14 : $i]:
% 0.44/0.71         ((zip_tseitin_0 @ X13 @ X14) | ((X13) = (k1_xboole_0)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.44/0.71  thf('23', plain,
% 0.44/0.71      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.44/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.44/0.71      inference('simplify', [status(thm)], ['7'])).
% 0.44/0.71  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.44/0.71  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.44/0.71  thf(zf_stmt_5, axiom,
% 0.44/0.71    (![A:$i,B:$i,C:$i]:
% 0.44/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.71       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.44/0.71         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.71           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.71             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.44/0.71  thf('24', plain,
% 0.44/0.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.71         (~ (zip_tseitin_0 @ X18 @ X19)
% 0.44/0.71          | (zip_tseitin_1 @ X20 @ X18 @ X19)
% 0.44/0.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.71  thf('25', plain,
% 0.44/0.71      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ sk_A @ sk_B)
% 0.44/0.71        | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.44/0.71      inference('sup-', [status(thm)], ['23', '24'])).
% 0.44/0.71  thf('26', plain,
% 0.44/0.71      ((((sk_A) = (k1_xboole_0))
% 0.44/0.71        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ sk_A @ sk_B))),
% 0.44/0.71      inference('sup-', [status(thm)], ['22', '25'])).
% 0.44/0.71  thf('27', plain, (((sk_A) != (k1_xboole_0))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('28', plain, ((zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ sk_A @ sk_B)),
% 0.44/0.71      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.44/0.71  thf('29', plain,
% 0.44/0.71      (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C_1)))),
% 0.44/0.71      inference('demod', [status(thm)], ['21', '28'])).
% 0.44/0.71  thf('30', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.44/0.71      inference('sup+', [status(thm)], ['10', '29'])).
% 0.44/0.71  thf('31', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('32', plain,
% 0.44/0.71      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.71         (~ (v1_funct_2 @ X17 @ X15 @ X16)
% 0.44/0.71          | ((X15) = (k1_relset_1 @ X15 @ X16 @ X17))
% 0.44/0.71          | ~ (zip_tseitin_1 @ X17 @ X16 @ X15))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.71  thf('33', plain,
% 0.44/0.71      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.44/0.71        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.71  thf('34', plain,
% 0.44/0.71      (![X13 : $i, X14 : $i]:
% 0.44/0.71         ((zip_tseitin_0 @ X13 @ X14) | ((X13) = (k1_xboole_0)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.44/0.71  thf('35', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('36', plain,
% 0.44/0.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.71         (~ (zip_tseitin_0 @ X18 @ X19)
% 0.44/0.71          | (zip_tseitin_1 @ X20 @ X18 @ X19)
% 0.44/0.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18))))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.71  thf('37', plain,
% 0.44/0.71      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.44/0.71      inference('sup-', [status(thm)], ['35', '36'])).
% 0.44/0.71  thf('38', plain,
% 0.44/0.71      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.44/0.71      inference('sup-', [status(thm)], ['34', '37'])).
% 0.44/0.71  thf('39', plain, (((sk_A) != (k1_xboole_0))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('40', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.44/0.71      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.44/0.71  thf('41', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('42', plain,
% 0.44/0.71      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.71         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.44/0.71          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.44/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.44/0.71  thf('43', plain,
% 0.44/0.71      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.44/0.71      inference('sup-', [status(thm)], ['41', '42'])).
% 0.44/0.71  thf('44', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.44/0.71      inference('demod', [status(thm)], ['33', '40', '43'])).
% 0.44/0.71  thf(t9_funct_1, axiom,
% 0.44/0.71    (![A:$i]:
% 0.44/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.71       ( ![B:$i]:
% 0.44/0.71         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.71           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.44/0.71               ( ![C:$i]:
% 0.44/0.71                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.44/0.71                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 0.44/0.71             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.44/0.71  thf('45', plain,
% 0.44/0.71      (![X5 : $i, X6 : $i]:
% 0.44/0.71         (~ (v1_relat_1 @ X5)
% 0.44/0.71          | ~ (v1_funct_1 @ X5)
% 0.44/0.71          | ((X6) = (X5))
% 0.44/0.71          | (r2_hidden @ (sk_C @ X5 @ X6) @ (k1_relat_1 @ X6))
% 0.44/0.71          | ((k1_relat_1 @ X6) != (k1_relat_1 @ X5))
% 0.44/0.71          | ~ (v1_funct_1 @ X6)
% 0.44/0.71          | ~ (v1_relat_1 @ X6))),
% 0.44/0.71      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.44/0.71  thf('46', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (((sk_B) != (k1_relat_1 @ X0))
% 0.44/0.71          | ~ (v1_relat_1 @ sk_D)
% 0.44/0.71          | ~ (v1_funct_1 @ sk_D)
% 0.44/0.71          | (r2_hidden @ (sk_C @ X0 @ sk_D) @ (k1_relat_1 @ sk_D))
% 0.44/0.71          | ((sk_D) = (X0))
% 0.44/0.71          | ~ (v1_funct_1 @ X0)
% 0.44/0.71          | ~ (v1_relat_1 @ X0))),
% 0.44/0.71      inference('sup-', [status(thm)], ['44', '45'])).
% 0.44/0.71  thf('47', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf(cc2_relat_1, axiom,
% 0.44/0.71    (![A:$i]:
% 0.44/0.71     ( ( v1_relat_1 @ A ) =>
% 0.44/0.71       ( ![B:$i]:
% 0.44/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.44/0.71  thf('48', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.44/0.71          | (v1_relat_1 @ X0)
% 0.44/0.71          | ~ (v1_relat_1 @ X1))),
% 0.44/0.71      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.44/0.71  thf('49', plain,
% 0.44/0.71      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.44/0.71      inference('sup-', [status(thm)], ['47', '48'])).
% 0.44/0.71  thf(fc6_relat_1, axiom,
% 0.44/0.71    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.44/0.71  thf('50', plain,
% 0.44/0.71      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.44/0.71      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.44/0.71  thf('51', plain, ((v1_relat_1 @ sk_D)),
% 0.44/0.71      inference('demod', [status(thm)], ['49', '50'])).
% 0.44/0.71  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('53', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.44/0.71      inference('demod', [status(thm)], ['33', '40', '43'])).
% 0.44/0.71  thf('54', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (((sk_B) != (k1_relat_1 @ X0))
% 0.44/0.71          | (r2_hidden @ (sk_C @ X0 @ sk_D) @ sk_B)
% 0.44/0.71          | ((sk_D) = (X0))
% 0.44/0.71          | ~ (v1_funct_1 @ X0)
% 0.44/0.71          | ~ (v1_relat_1 @ X0))),
% 0.44/0.71      inference('demod', [status(thm)], ['46', '51', '52', '53'])).
% 0.44/0.71  thf('55', plain,
% 0.44/0.71      ((((sk_B) != (sk_B))
% 0.44/0.71        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.44/0.71        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.44/0.71        | ((sk_D) = (k2_funct_1 @ sk_C_1))
% 0.44/0.71        | (r2_hidden @ (sk_C @ (k2_funct_1 @ sk_C_1) @ sk_D) @ sk_B))),
% 0.44/0.71      inference('sup-', [status(thm)], ['30', '54'])).
% 0.44/0.71  thf('56', plain,
% 0.44/0.71      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.44/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.44/0.71      inference('simplify', [status(thm)], ['7'])).
% 0.44/0.71  thf('57', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.44/0.71          | (v1_relat_1 @ X0)
% 0.44/0.71          | ~ (v1_relat_1 @ X1))),
% 0.44/0.71      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.44/0.71  thf('58', plain,
% 0.44/0.71      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))
% 0.44/0.71        | (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['56', '57'])).
% 0.44/0.71  thf('59', plain,
% 0.44/0.71      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.44/0.71      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.44/0.71  thf('60', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 0.44/0.71      inference('demod', [status(thm)], ['58', '59'])).
% 0.44/0.71  thf('61', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('62', plain,
% 0.44/0.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.71         (~ (v2_funct_1 @ X21)
% 0.44/0.71          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.44/0.71          | (v1_funct_1 @ (k2_funct_1 @ X21))
% 0.44/0.71          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.44/0.71          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.44/0.71          | ~ (v1_funct_1 @ X21))),
% 0.44/0.71      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.44/0.71  thf('63', plain,
% 0.44/0.71      ((~ (v1_funct_1 @ sk_C_1)
% 0.44/0.71        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.44/0.71        | (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.44/0.71        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 0.44/0.71        | ~ (v2_funct_1 @ sk_C_1))),
% 0.44/0.71      inference('sup-', [status(thm)], ['61', '62'])).
% 0.44/0.71  thf('64', plain, ((v1_funct_1 @ sk_C_1)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('65', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('66', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('67', plain, ((v2_funct_1 @ sk_C_1)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('68', plain,
% 0.44/0.71      (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)) | ((sk_B) != (sk_B)))),
% 0.44/0.71      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.44/0.71  thf('69', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 0.44/0.71      inference('simplify', [status(thm)], ['68'])).
% 0.44/0.71  thf('70', plain,
% 0.44/0.71      ((((sk_B) != (sk_B))
% 0.44/0.71        | ((sk_D) = (k2_funct_1 @ sk_C_1))
% 0.44/0.71        | (r2_hidden @ (sk_C @ (k2_funct_1 @ sk_C_1) @ sk_D) @ sk_B))),
% 0.44/0.71      inference('demod', [status(thm)], ['55', '60', '69'])).
% 0.44/0.71  thf('71', plain,
% 0.44/0.71      (((r2_hidden @ (sk_C @ (k2_funct_1 @ sk_C_1) @ sk_D) @ sk_B)
% 0.44/0.71        | ((sk_D) = (k2_funct_1 @ sk_C_1)))),
% 0.44/0.71      inference('simplify', [status(thm)], ['70'])).
% 0.44/0.71  thf('72', plain, (((sk_D) != (k2_funct_1 @ sk_C_1))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('73', plain,
% 0.44/0.71      ((r2_hidden @ (sk_C @ (k2_funct_1 @ sk_C_1) @ sk_D) @ sk_B)),
% 0.44/0.71      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 0.44/0.71  thf('74', plain,
% 0.44/0.71      (![X28 : $i, X29 : $i]:
% 0.44/0.71         ((r2_hidden @ X28 @ sk_A)
% 0.44/0.71          | ((k1_funct_1 @ sk_D @ X29) != (X28))
% 0.44/0.71          | ~ (r2_hidden @ X29 @ sk_B))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('75', plain,
% 0.44/0.71      (![X29 : $i]:
% 0.44/0.71         (~ (r2_hidden @ X29 @ sk_B)
% 0.44/0.71          | (r2_hidden @ (k1_funct_1 @ sk_D @ X29) @ sk_A))),
% 0.44/0.71      inference('simplify', [status(thm)], ['74'])).
% 0.44/0.71  thf('76', plain,
% 0.44/0.71      ((r2_hidden @ 
% 0.44/0.71        (k1_funct_1 @ sk_D @ (sk_C @ (k2_funct_1 @ sk_C_1) @ sk_D)) @ sk_A)),
% 0.44/0.71      inference('sup-', [status(thm)], ['73', '75'])).
% 0.44/0.71  thf('77', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf(t32_funct_2, axiom,
% 0.44/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.44/0.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.71       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.44/0.71         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.44/0.71           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.44/0.71             ( C ) ) ) ) ))).
% 0.44/0.71  thf('78', plain,
% 0.44/0.71      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.44/0.71         (~ (r2_hidden @ X24 @ X25)
% 0.44/0.71          | ((X26) = (k1_xboole_0))
% 0.44/0.71          | ~ (v1_funct_1 @ X27)
% 0.44/0.71          | ~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.44/0.71          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.44/0.71          | ((k1_funct_1 @ (k2_funct_1 @ X27) @ (k1_funct_1 @ X27 @ X24))
% 0.44/0.71              = (X24))
% 0.44/0.71          | ~ (v2_funct_1 @ X27))),
% 0.44/0.71      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.44/0.71  thf('79', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (~ (v2_funct_1 @ sk_C_1)
% 0.44/0.71          | ((k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ (k1_funct_1 @ sk_C_1 @ X0))
% 0.44/0.71              = (X0))
% 0.44/0.71          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.44/0.71          | ~ (v1_funct_1 @ sk_C_1)
% 0.44/0.71          | ((sk_B) = (k1_xboole_0))
% 0.44/0.71          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.44/0.71      inference('sup-', [status(thm)], ['77', '78'])).
% 0.44/0.71  thf('80', plain, ((v2_funct_1 @ sk_C_1)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('81', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('82', plain, ((v1_funct_1 @ sk_C_1)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('83', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (((k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ (k1_funct_1 @ sk_C_1 @ X0))
% 0.44/0.71            = (X0))
% 0.44/0.71          | ((sk_B) = (k1_xboole_0))
% 0.44/0.71          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.44/0.71      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 0.44/0.71  thf('84', plain, (((sk_B) != (k1_xboole_0))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('85', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (((k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ (k1_funct_1 @ sk_C_1 @ X0))
% 0.44/0.71            = (X0))
% 0.44/0.71          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.44/0.71      inference('simplify_reflect-', [status(thm)], ['83', '84'])).
% 0.44/0.71  thf('86', plain,
% 0.44/0.71      (((k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.44/0.71         (k1_funct_1 @ sk_C_1 @ 
% 0.44/0.71          (k1_funct_1 @ sk_D @ (sk_C @ (k2_funct_1 @ sk_C_1) @ sk_D))))
% 0.44/0.71         = (k1_funct_1 @ sk_D @ (sk_C @ (k2_funct_1 @ sk_C_1) @ sk_D)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['76', '85'])).
% 0.44/0.71  thf('87', plain,
% 0.44/0.71      ((r2_hidden @ (sk_C @ (k2_funct_1 @ sk_C_1) @ sk_D) @ sk_B)),
% 0.44/0.71      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 0.44/0.71  thf('88', plain,
% 0.44/0.71      (![X28 : $i, X29 : $i]:
% 0.44/0.71         (((k1_funct_1 @ sk_C_1 @ X28) = (X29))
% 0.44/0.71          | ((k1_funct_1 @ sk_D @ X29) != (X28))
% 0.44/0.71          | ~ (r2_hidden @ X29 @ sk_B))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('89', plain,
% 0.44/0.71      (![X29 : $i]:
% 0.44/0.71         (~ (r2_hidden @ X29 @ sk_B)
% 0.44/0.71          | ((k1_funct_1 @ sk_C_1 @ (k1_funct_1 @ sk_D @ X29)) = (X29)))),
% 0.44/0.71      inference('simplify', [status(thm)], ['88'])).
% 0.44/0.71  thf('90', plain,
% 0.44/0.71      (((k1_funct_1 @ sk_C_1 @ 
% 0.44/0.71         (k1_funct_1 @ sk_D @ (sk_C @ (k2_funct_1 @ sk_C_1) @ sk_D)))
% 0.44/0.71         = (sk_C @ (k2_funct_1 @ sk_C_1) @ sk_D))),
% 0.44/0.71      inference('sup-', [status(thm)], ['87', '89'])).
% 0.44/0.71  thf('91', plain,
% 0.44/0.71      (((k1_funct_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.44/0.71         (sk_C @ (k2_funct_1 @ sk_C_1) @ sk_D))
% 0.44/0.71         = (k1_funct_1 @ sk_D @ (sk_C @ (k2_funct_1 @ sk_C_1) @ sk_D)))),
% 0.44/0.71      inference('demod', [status(thm)], ['86', '90'])).
% 0.44/0.71  thf('92', plain,
% 0.44/0.71      (![X5 : $i, X6 : $i]:
% 0.44/0.71         (~ (v1_relat_1 @ X5)
% 0.44/0.71          | ~ (v1_funct_1 @ X5)
% 0.44/0.71          | ((X6) = (X5))
% 0.44/0.71          | ((k1_funct_1 @ X6 @ (sk_C @ X5 @ X6))
% 0.44/0.71              != (k1_funct_1 @ X5 @ (sk_C @ X5 @ X6)))
% 0.44/0.71          | ((k1_relat_1 @ X6) != (k1_relat_1 @ X5))
% 0.44/0.71          | ~ (v1_funct_1 @ X6)
% 0.44/0.71          | ~ (v1_relat_1 @ X6))),
% 0.44/0.71      inference('cnf', [status(esa)], [t9_funct_1])).
% 0.44/0.71  thf('93', plain,
% 0.44/0.71      ((((k1_funct_1 @ sk_D @ (sk_C @ (k2_funct_1 @ sk_C_1) @ sk_D))
% 0.44/0.71          != (k1_funct_1 @ sk_D @ (sk_C @ (k2_funct_1 @ sk_C_1) @ sk_D)))
% 0.44/0.71        | ~ (v1_relat_1 @ sk_D)
% 0.44/0.71        | ~ (v1_funct_1 @ sk_D)
% 0.44/0.71        | ((k1_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 0.44/0.71        | ((sk_D) = (k2_funct_1 @ sk_C_1))
% 0.44/0.71        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.44/0.71        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['91', '92'])).
% 0.44/0.71  thf('94', plain, ((v1_relat_1 @ sk_D)),
% 0.44/0.71      inference('demod', [status(thm)], ['49', '50'])).
% 0.44/0.71  thf('95', plain, ((v1_funct_1 @ sk_D)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('96', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.44/0.71      inference('demod', [status(thm)], ['33', '40', '43'])).
% 0.44/0.71  thf('97', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.44/0.71      inference('sup+', [status(thm)], ['10', '29'])).
% 0.44/0.71  thf('98', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 0.44/0.71      inference('simplify', [status(thm)], ['68'])).
% 0.44/0.71  thf('99', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 0.44/0.71      inference('demod', [status(thm)], ['58', '59'])).
% 0.44/0.71  thf('100', plain,
% 0.44/0.71      ((((k1_funct_1 @ sk_D @ (sk_C @ (k2_funct_1 @ sk_C_1) @ sk_D))
% 0.44/0.71          != (k1_funct_1 @ sk_D @ (sk_C @ (k2_funct_1 @ sk_C_1) @ sk_D)))
% 0.44/0.71        | ((sk_B) != (sk_B))
% 0.44/0.71        | ((sk_D) = (k2_funct_1 @ sk_C_1)))),
% 0.44/0.71      inference('demod', [status(thm)],
% 0.44/0.71                ['93', '94', '95', '96', '97', '98', '99'])).
% 0.44/0.71  thf('101', plain, (((sk_D) = (k2_funct_1 @ sk_C_1))),
% 0.44/0.71      inference('simplify', [status(thm)], ['100'])).
% 0.44/0.71  thf('102', plain, (((sk_D) != (k2_funct_1 @ sk_C_1))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('103', plain, ($false),
% 0.44/0.71      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 0.44/0.71  
% 0.44/0.71  % SZS output end Refutation
% 0.44/0.71  
% 0.44/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
