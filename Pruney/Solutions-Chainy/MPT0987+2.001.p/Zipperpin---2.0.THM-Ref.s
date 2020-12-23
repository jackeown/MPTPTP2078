%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HX3NMZbCQe

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:51 EST 2020

% Result     : Theorem 9.38s
% Output     : Refutation 9.38s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 355 expanded)
%              Number of leaves         :   47 ( 126 expanded)
%              Depth                    :   15
%              Number of atoms          : 1158 (5598 expanded)
%              Number of equality atoms :   49 ( 104 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t33_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ~ ( v1_xboole_0 @ C )
         => ! [D: $i] :
              ( ( ( v1_funct_1 @ D )
                & ( v1_funct_2 @ D @ A @ B )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [E: $i] :
                  ( ( ( v1_funct_1 @ E )
                    & ( v1_funct_2 @ E @ B @ C )
                    & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
                 => ( ( ( v2_funct_2 @ D @ B )
                      & ( v2_funct_2 @ E @ C ) )
                   => ( v2_funct_2 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( v1_xboole_0 @ B )
       => ! [C: $i] :
            ( ~ ( v1_xboole_0 @ C )
           => ! [D: $i] :
                ( ( ( v1_funct_1 @ D )
                  & ( v1_funct_2 @ D @ A @ B )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
               => ! [E: $i] :
                    ( ( ( v1_funct_1 @ E )
                      & ( v1_funct_2 @ E @ B @ C )
                      & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
                   => ( ( ( v2_funct_2 @ D @ B )
                        & ( v2_funct_2 @ E @ C ) )
                     => ( v2_funct_2 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_funct_2])).

thf('0',plain,(
    ~ ( v2_funct_2 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_C @ sk_D @ sk_E ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
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

thf('2',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['6','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('19',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','16','19'])).

thf('21',plain,(
    ~ ( v2_funct_2 @ ( k1_partfun1 @ ( k1_relat_1 @ sk_D ) @ sk_B_1 @ sk_B_1 @ sk_C @ sk_D @ sk_E ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','16','19'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('26',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( ( k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48 )
        = ( k5_relat_1 @ X45 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ ( k1_relat_1 @ sk_D ) @ sk_B_1 @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ ( k1_relat_1 @ sk_D ) @ sk_B_1 @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ ( k1_relat_1 @ sk_D ) @ sk_B_1 @ sk_B_1 @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_partfun1 @ ( k1_relat_1 @ sk_D ) @ sk_B_1 @ sk_B_1 @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_funct_2 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_C ) ),
    inference(demod,[status(thm)],['21','32'])).

thf('34',plain,(
    v2_funct_2 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('35',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v2_funct_2 @ X38 @ X37 )
      | ( ( k2_relat_1 @ X38 )
        = X37 )
      | ~ ( v5_relat_1 @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v5_relat_1 @ sk_D @ sk_B_1 )
    | ( ( k2_relat_1 @ sk_D )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('43',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('44',plain,(
    v5_relat_1 @ sk_D @ sk_B_1 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B_1 ),
    inference(demod,[status(thm)],['36','41','44'])).

thf('46',plain,(
    v1_funct_2 @ sk_E @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('48',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('51',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B_1 ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('58',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['48','55','58'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('60',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        = ( k2_relat_1 @ sk_E ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('66',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        = ( k2_relat_1 @ sk_E ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('68',plain,(
    v2_funct_2 @ sk_E @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v2_funct_2 @ X38 @ X37 )
      | ( ( k2_relat_1 @ X38 )
        = X37 )
      | ~ ( v5_relat_1 @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v5_relat_1 @ sk_E @ sk_C )
    | ( ( k2_relat_1 @ sk_E )
      = sk_C ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['64','65'])).

thf('72',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('74',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['70','71','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        = sk_C )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','75'])).

thf('77',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['45','76'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('78',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('79',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('81',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['77','79','80'])).

thf('82',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k2_relat_1 @ X38 )
       != X37 )
      | ( v2_funct_2 @ X38 @ X37 )
      | ~ ( v5_relat_1 @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('83',plain,(
    ! [X38: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ~ ( v5_relat_1 @ X38 @ ( k2_relat_1 @ X38 ) )
      | ( v2_funct_2 @ X38 @ ( k2_relat_1 @ X38 ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['78'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('85',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( v5_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X38: $i] :
      ( ( v2_funct_2 @ X38 @ ( k2_relat_1 @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(clc,[status(thm)],['83','86'])).

thf('88',plain,
    ( ( v2_funct_2 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_C )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup+',[status(thm)],['81','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('91',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ sk_D ) @ sk_B_1 @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ sk_D ) @ sk_B_1 @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ sk_D ) @ sk_B_1 @ sk_B_1 @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ sk_D ) @ sk_B_1 @ sk_B_1 @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('98',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('99',plain,(
    v1_relat_1 @ ( k1_partfun1 @ ( k1_relat_1 @ sk_D ) @ sk_B_1 @ sk_B_1 @ sk_C @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k1_partfun1 @ ( k1_relat_1 @ sk_D ) @ sk_B_1 @ sk_B_1 @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('101',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    v2_funct_2 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['88','101'])).

thf('103',plain,(
    $false ),
    inference(demod,[status(thm)],['33','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HX3NMZbCQe
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:30:03 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 9.38/9.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.38/9.59  % Solved by: fo/fo7.sh
% 9.38/9.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.38/9.59  % done 5081 iterations in 9.149s
% 9.38/9.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.38/9.59  % SZS output start Refutation
% 9.38/9.59  thf(sk_E_type, type, sk_E: $i).
% 9.38/9.59  thf(sk_A_type, type, sk_A: $i).
% 9.38/9.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 9.38/9.59  thf(sk_B_type, type, sk_B: $i > $i).
% 9.38/9.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 9.38/9.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.38/9.59  thf(sk_C_type, type, sk_C: $i).
% 9.38/9.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.38/9.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 9.38/9.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 9.38/9.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 9.38/9.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 9.38/9.59  thf(sk_D_type, type, sk_D: $i).
% 9.38/9.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 9.38/9.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.38/9.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.38/9.59  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 9.38/9.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 9.38/9.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 9.38/9.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.38/9.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.38/9.59  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 9.38/9.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 9.38/9.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.38/9.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 9.38/9.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.38/9.59  thf(t33_funct_2, conjecture,
% 9.38/9.59    (![A:$i,B:$i]:
% 9.38/9.59     ( ( ~( v1_xboole_0 @ B ) ) =>
% 9.38/9.59       ( ![C:$i]:
% 9.38/9.59         ( ( ~( v1_xboole_0 @ C ) ) =>
% 9.38/9.59           ( ![D:$i]:
% 9.38/9.59             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 9.38/9.59                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.38/9.59               ( ![E:$i]:
% 9.38/9.59                 ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 9.38/9.59                     ( m1_subset_1 @
% 9.38/9.59                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 9.38/9.59                   ( ( ( v2_funct_2 @ D @ B ) & ( v2_funct_2 @ E @ C ) ) =>
% 9.38/9.59                     ( v2_funct_2 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) @ C ) ) ) ) ) ) ) ) ))).
% 9.38/9.59  thf(zf_stmt_0, negated_conjecture,
% 9.38/9.59    (~( ![A:$i,B:$i]:
% 9.38/9.59        ( ( ~( v1_xboole_0 @ B ) ) =>
% 9.38/9.59          ( ![C:$i]:
% 9.38/9.59            ( ( ~( v1_xboole_0 @ C ) ) =>
% 9.38/9.59              ( ![D:$i]:
% 9.38/9.59                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 9.38/9.59                    ( m1_subset_1 @
% 9.38/9.59                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.38/9.59                  ( ![E:$i]:
% 9.38/9.59                    ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 9.38/9.59                        ( m1_subset_1 @
% 9.38/9.59                          E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 9.38/9.59                      ( ( ( v2_funct_2 @ D @ B ) & ( v2_funct_2 @ E @ C ) ) =>
% 9.38/9.59                        ( v2_funct_2 @
% 9.38/9.59                          ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) @ C ) ) ) ) ) ) ) ) ) )),
% 9.38/9.59    inference('cnf.neg', [status(esa)], [t33_funct_2])).
% 9.38/9.59  thf('0', plain,
% 9.38/9.59      (~ (v2_funct_2 @ 
% 9.38/9.59          (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_C @ sk_D @ sk_E) @ sk_C)),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf(d1_funct_2, axiom,
% 9.38/9.59    (![A:$i,B:$i,C:$i]:
% 9.38/9.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.38/9.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 9.38/9.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 9.38/9.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 9.38/9.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 9.38/9.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 9.38/9.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 9.38/9.59  thf(zf_stmt_1, axiom,
% 9.38/9.59    (![C:$i,B:$i,A:$i]:
% 9.38/9.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 9.38/9.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 9.38/9.59  thf('2', plain,
% 9.38/9.59      (![X31 : $i, X32 : $i, X33 : $i]:
% 9.38/9.59         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 9.38/9.59          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 9.38/9.59          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.38/9.59  thf('3', plain,
% 9.38/9.59      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 9.38/9.59        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 9.38/9.59      inference('sup-', [status(thm)], ['1', '2'])).
% 9.38/9.59  thf('4', plain,
% 9.38/9.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 9.38/9.59  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 9.38/9.59  thf(zf_stmt_4, axiom,
% 9.38/9.59    (![B:$i,A:$i]:
% 9.38/9.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 9.38/9.59       ( zip_tseitin_0 @ B @ A ) ))).
% 9.38/9.59  thf(zf_stmt_5, axiom,
% 9.38/9.59    (![A:$i,B:$i,C:$i]:
% 9.38/9.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.38/9.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 9.38/9.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 9.38/9.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 9.38/9.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 9.38/9.59  thf('5', plain,
% 9.38/9.59      (![X34 : $i, X35 : $i, X36 : $i]:
% 9.38/9.59         (~ (zip_tseitin_0 @ X34 @ X35)
% 9.38/9.59          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 9.38/9.59          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 9.38/9.59  thf('6', plain,
% 9.38/9.59      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 9.38/9.59        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 9.38/9.59      inference('sup-', [status(thm)], ['4', '5'])).
% 9.38/9.59  thf('7', plain,
% 9.38/9.59      (![X29 : $i, X30 : $i]:
% 9.38/9.59         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_4])).
% 9.38/9.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 9.38/9.59  thf('8', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 9.38/9.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.38/9.59  thf('9', plain,
% 9.38/9.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.38/9.59         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 9.38/9.59      inference('sup+', [status(thm)], ['7', '8'])).
% 9.38/9.59  thf(d1_xboole_0, axiom,
% 9.38/9.59    (![A:$i]:
% 9.38/9.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 9.38/9.59  thf('10', plain,
% 9.38/9.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 9.38/9.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 9.38/9.59  thf(t7_ordinal1, axiom,
% 9.38/9.59    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.38/9.59  thf('11', plain,
% 9.38/9.59      (![X18 : $i, X19 : $i]:
% 9.38/9.59         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 9.38/9.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 9.38/9.59  thf('12', plain,
% 9.38/9.59      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 9.38/9.59      inference('sup-', [status(thm)], ['10', '11'])).
% 9.38/9.59  thf('13', plain,
% 9.38/9.59      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 9.38/9.59      inference('sup-', [status(thm)], ['9', '12'])).
% 9.38/9.59  thf('14', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf('15', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 9.38/9.59      inference('sup-', [status(thm)], ['13', '14'])).
% 9.38/9.59  thf('16', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 9.38/9.59      inference('demod', [status(thm)], ['6', '15'])).
% 9.38/9.59  thf('17', plain,
% 9.38/9.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf(redefinition_k1_relset_1, axiom,
% 9.38/9.59    (![A:$i,B:$i,C:$i]:
% 9.38/9.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.38/9.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 9.38/9.59  thf('18', plain,
% 9.38/9.59      (![X26 : $i, X27 : $i, X28 : $i]:
% 9.38/9.59         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 9.38/9.59          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 9.38/9.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 9.38/9.59  thf('19', plain,
% 9.38/9.59      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 9.38/9.59      inference('sup-', [status(thm)], ['17', '18'])).
% 9.38/9.59  thf('20', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 9.38/9.59      inference('demod', [status(thm)], ['3', '16', '19'])).
% 9.38/9.59  thf('21', plain,
% 9.38/9.59      (~ (v2_funct_2 @ 
% 9.38/9.59          (k1_partfun1 @ (k1_relat_1 @ sk_D) @ sk_B_1 @ sk_B_1 @ sk_C @ sk_D @ 
% 9.38/9.59           sk_E) @ 
% 9.38/9.59          sk_C)),
% 9.38/9.59      inference('demod', [status(thm)], ['0', '20'])).
% 9.38/9.59  thf('22', plain,
% 9.38/9.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf('23', plain,
% 9.38/9.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf('24', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 9.38/9.59      inference('demod', [status(thm)], ['3', '16', '19'])).
% 9.38/9.59  thf('25', plain,
% 9.38/9.59      ((m1_subset_1 @ sk_D @ 
% 9.38/9.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B_1)))),
% 9.38/9.59      inference('demod', [status(thm)], ['23', '24'])).
% 9.38/9.59  thf(redefinition_k1_partfun1, axiom,
% 9.38/9.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 9.38/9.59     ( ( ( v1_funct_1 @ E ) & 
% 9.38/9.59         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 9.38/9.59         ( v1_funct_1 @ F ) & 
% 9.38/9.59         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 9.38/9.59       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 9.38/9.59  thf('26', plain,
% 9.38/9.59      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 9.38/9.59         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 9.38/9.59          | ~ (v1_funct_1 @ X45)
% 9.38/9.59          | ~ (v1_funct_1 @ X48)
% 9.38/9.59          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 9.38/9.59          | ((k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48)
% 9.38/9.59              = (k5_relat_1 @ X45 @ X48)))),
% 9.38/9.59      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 9.38/9.59  thf('27', plain,
% 9.38/9.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.38/9.59         (((k1_partfun1 @ (k1_relat_1 @ sk_D) @ sk_B_1 @ X2 @ X1 @ sk_D @ X0)
% 9.38/9.59            = (k5_relat_1 @ sk_D @ X0))
% 9.38/9.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 9.38/9.59          | ~ (v1_funct_1 @ X0)
% 9.38/9.59          | ~ (v1_funct_1 @ sk_D))),
% 9.38/9.59      inference('sup-', [status(thm)], ['25', '26'])).
% 9.38/9.59  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf('29', plain,
% 9.38/9.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.38/9.59         (((k1_partfun1 @ (k1_relat_1 @ sk_D) @ sk_B_1 @ X2 @ X1 @ sk_D @ X0)
% 9.38/9.59            = (k5_relat_1 @ sk_D @ X0))
% 9.38/9.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 9.38/9.59          | ~ (v1_funct_1 @ X0))),
% 9.38/9.59      inference('demod', [status(thm)], ['27', '28'])).
% 9.38/9.59  thf('30', plain,
% 9.38/9.59      ((~ (v1_funct_1 @ sk_E)
% 9.38/9.59        | ((k1_partfun1 @ (k1_relat_1 @ sk_D) @ sk_B_1 @ sk_B_1 @ sk_C @ 
% 9.38/9.59            sk_D @ sk_E) = (k5_relat_1 @ sk_D @ sk_E)))),
% 9.38/9.59      inference('sup-', [status(thm)], ['22', '29'])).
% 9.38/9.59  thf('31', plain, ((v1_funct_1 @ sk_E)),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf('32', plain,
% 9.38/9.59      (((k1_partfun1 @ (k1_relat_1 @ sk_D) @ sk_B_1 @ sk_B_1 @ sk_C @ sk_D @ 
% 9.38/9.59         sk_E) = (k5_relat_1 @ sk_D @ sk_E))),
% 9.38/9.59      inference('demod', [status(thm)], ['30', '31'])).
% 9.38/9.59  thf('33', plain, (~ (v2_funct_2 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_C)),
% 9.38/9.59      inference('demod', [status(thm)], ['21', '32'])).
% 9.38/9.59  thf('34', plain, ((v2_funct_2 @ sk_D @ sk_B_1)),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf(d3_funct_2, axiom,
% 9.38/9.59    (![A:$i,B:$i]:
% 9.38/9.59     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 9.38/9.59       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 9.38/9.59  thf('35', plain,
% 9.38/9.59      (![X37 : $i, X38 : $i]:
% 9.38/9.59         (~ (v2_funct_2 @ X38 @ X37)
% 9.38/9.59          | ((k2_relat_1 @ X38) = (X37))
% 9.38/9.59          | ~ (v5_relat_1 @ X38 @ X37)
% 9.38/9.59          | ~ (v1_relat_1 @ X38))),
% 9.38/9.59      inference('cnf', [status(esa)], [d3_funct_2])).
% 9.38/9.59  thf('36', plain,
% 9.38/9.59      ((~ (v1_relat_1 @ sk_D)
% 9.38/9.59        | ~ (v5_relat_1 @ sk_D @ sk_B_1)
% 9.38/9.59        | ((k2_relat_1 @ sk_D) = (sk_B_1)))),
% 9.38/9.59      inference('sup-', [status(thm)], ['34', '35'])).
% 9.38/9.59  thf('37', plain,
% 9.38/9.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf(cc2_relat_1, axiom,
% 9.38/9.59    (![A:$i]:
% 9.38/9.59     ( ( v1_relat_1 @ A ) =>
% 9.38/9.59       ( ![B:$i]:
% 9.38/9.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 9.38/9.59  thf('38', plain,
% 9.38/9.59      (![X10 : $i, X11 : $i]:
% 9.38/9.59         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 9.38/9.59          | (v1_relat_1 @ X10)
% 9.38/9.59          | ~ (v1_relat_1 @ X11))),
% 9.38/9.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 9.38/9.59  thf('39', plain,
% 9.38/9.59      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 9.38/9.59      inference('sup-', [status(thm)], ['37', '38'])).
% 9.38/9.59  thf(fc6_relat_1, axiom,
% 9.38/9.59    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 9.38/9.59  thf('40', plain,
% 9.38/9.59      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 9.38/9.59      inference('cnf', [status(esa)], [fc6_relat_1])).
% 9.38/9.59  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 9.38/9.59      inference('demod', [status(thm)], ['39', '40'])).
% 9.38/9.59  thf('42', plain,
% 9.38/9.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf(cc2_relset_1, axiom,
% 9.38/9.59    (![A:$i,B:$i,C:$i]:
% 9.38/9.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.38/9.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 9.38/9.59  thf('43', plain,
% 9.38/9.59      (![X23 : $i, X24 : $i, X25 : $i]:
% 9.38/9.59         ((v5_relat_1 @ X23 @ X25)
% 9.38/9.59          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 9.38/9.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 9.38/9.59  thf('44', plain, ((v5_relat_1 @ sk_D @ sk_B_1)),
% 9.38/9.59      inference('sup-', [status(thm)], ['42', '43'])).
% 9.38/9.59  thf('45', plain, (((k2_relat_1 @ sk_D) = (sk_B_1))),
% 9.38/9.59      inference('demod', [status(thm)], ['36', '41', '44'])).
% 9.38/9.59  thf('46', plain, ((v1_funct_2 @ sk_E @ sk_B_1 @ sk_C)),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf('47', plain,
% 9.38/9.59      (![X31 : $i, X32 : $i, X33 : $i]:
% 9.38/9.59         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 9.38/9.59          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 9.38/9.59          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 9.38/9.59  thf('48', plain,
% 9.38/9.59      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B_1)
% 9.38/9.59        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C @ sk_E)))),
% 9.38/9.59      inference('sup-', [status(thm)], ['46', '47'])).
% 9.38/9.59  thf('49', plain,
% 9.38/9.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf('50', plain,
% 9.38/9.59      (![X34 : $i, X35 : $i, X36 : $i]:
% 9.38/9.59         (~ (zip_tseitin_0 @ X34 @ X35)
% 9.38/9.59          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 9.38/9.59          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 9.38/9.59  thf('51', plain,
% 9.38/9.59      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B_1)
% 9.38/9.59        | ~ (zip_tseitin_0 @ sk_C @ sk_B_1))),
% 9.38/9.59      inference('sup-', [status(thm)], ['49', '50'])).
% 9.38/9.59  thf('52', plain,
% 9.38/9.59      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 9.38/9.59      inference('sup-', [status(thm)], ['9', '12'])).
% 9.38/9.59  thf('53', plain, (~ (v1_xboole_0 @ sk_C)),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf('54', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 9.38/9.59      inference('sup-', [status(thm)], ['52', '53'])).
% 9.38/9.59  thf('55', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B_1)),
% 9.38/9.59      inference('demod', [status(thm)], ['51', '54'])).
% 9.38/9.59  thf('56', plain,
% 9.38/9.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf('57', plain,
% 9.38/9.59      (![X26 : $i, X27 : $i, X28 : $i]:
% 9.38/9.59         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 9.38/9.59          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 9.38/9.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 9.38/9.59  thf('58', plain,
% 9.38/9.59      (((k1_relset_1 @ sk_B_1 @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 9.38/9.59      inference('sup-', [status(thm)], ['56', '57'])).
% 9.38/9.59  thf('59', plain, (((sk_B_1) = (k1_relat_1 @ sk_E))),
% 9.38/9.59      inference('demod', [status(thm)], ['48', '55', '58'])).
% 9.38/9.59  thf(t47_relat_1, axiom,
% 9.38/9.59    (![A:$i]:
% 9.38/9.59     ( ( v1_relat_1 @ A ) =>
% 9.38/9.59       ( ![B:$i]:
% 9.38/9.59         ( ( v1_relat_1 @ B ) =>
% 9.38/9.59           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 9.38/9.59             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 9.38/9.59  thf('60', plain,
% 9.38/9.59      (![X16 : $i, X17 : $i]:
% 9.38/9.59         (~ (v1_relat_1 @ X16)
% 9.38/9.59          | ((k2_relat_1 @ (k5_relat_1 @ X16 @ X17)) = (k2_relat_1 @ X17))
% 9.38/9.59          | ~ (r1_tarski @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X16))
% 9.38/9.59          | ~ (v1_relat_1 @ X17))),
% 9.38/9.59      inference('cnf', [status(esa)], [t47_relat_1])).
% 9.38/9.59  thf('61', plain,
% 9.38/9.59      (![X0 : $i]:
% 9.38/9.59         (~ (r1_tarski @ sk_B_1 @ (k2_relat_1 @ X0))
% 9.38/9.59          | ~ (v1_relat_1 @ sk_E)
% 9.38/9.59          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ sk_E)) = (k2_relat_1 @ sk_E))
% 9.38/9.59          | ~ (v1_relat_1 @ X0))),
% 9.38/9.59      inference('sup-', [status(thm)], ['59', '60'])).
% 9.38/9.59  thf('62', plain,
% 9.38/9.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf('63', plain,
% 9.38/9.59      (![X10 : $i, X11 : $i]:
% 9.38/9.59         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 9.38/9.59          | (v1_relat_1 @ X10)
% 9.38/9.59          | ~ (v1_relat_1 @ X11))),
% 9.38/9.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 9.38/9.59  thf('64', plain,
% 9.38/9.59      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)) | (v1_relat_1 @ sk_E))),
% 9.38/9.59      inference('sup-', [status(thm)], ['62', '63'])).
% 9.38/9.59  thf('65', plain,
% 9.38/9.59      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 9.38/9.59      inference('cnf', [status(esa)], [fc6_relat_1])).
% 9.38/9.59  thf('66', plain, ((v1_relat_1 @ sk_E)),
% 9.38/9.59      inference('demod', [status(thm)], ['64', '65'])).
% 9.38/9.59  thf('67', plain,
% 9.38/9.59      (![X0 : $i]:
% 9.38/9.59         (~ (r1_tarski @ sk_B_1 @ (k2_relat_1 @ X0))
% 9.38/9.59          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ sk_E)) = (k2_relat_1 @ sk_E))
% 9.38/9.59          | ~ (v1_relat_1 @ X0))),
% 9.38/9.59      inference('demod', [status(thm)], ['61', '66'])).
% 9.38/9.59  thf('68', plain, ((v2_funct_2 @ sk_E @ sk_C)),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf('69', plain,
% 9.38/9.59      (![X37 : $i, X38 : $i]:
% 9.38/9.59         (~ (v2_funct_2 @ X38 @ X37)
% 9.38/9.59          | ((k2_relat_1 @ X38) = (X37))
% 9.38/9.59          | ~ (v5_relat_1 @ X38 @ X37)
% 9.38/9.59          | ~ (v1_relat_1 @ X38))),
% 9.38/9.59      inference('cnf', [status(esa)], [d3_funct_2])).
% 9.38/9.59  thf('70', plain,
% 9.38/9.59      ((~ (v1_relat_1 @ sk_E)
% 9.38/9.59        | ~ (v5_relat_1 @ sk_E @ sk_C)
% 9.38/9.59        | ((k2_relat_1 @ sk_E) = (sk_C)))),
% 9.38/9.59      inference('sup-', [status(thm)], ['68', '69'])).
% 9.38/9.59  thf('71', plain, ((v1_relat_1 @ sk_E)),
% 9.38/9.59      inference('demod', [status(thm)], ['64', '65'])).
% 9.38/9.59  thf('72', plain,
% 9.38/9.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf('73', plain,
% 9.38/9.59      (![X23 : $i, X24 : $i, X25 : $i]:
% 9.38/9.59         ((v5_relat_1 @ X23 @ X25)
% 9.38/9.59          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 9.38/9.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 9.38/9.59  thf('74', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 9.38/9.59      inference('sup-', [status(thm)], ['72', '73'])).
% 9.38/9.59  thf('75', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 9.38/9.59      inference('demod', [status(thm)], ['70', '71', '74'])).
% 9.38/9.59  thf('76', plain,
% 9.38/9.59      (![X0 : $i]:
% 9.38/9.59         (~ (r1_tarski @ sk_B_1 @ (k2_relat_1 @ X0))
% 9.38/9.59          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ sk_E)) = (sk_C))
% 9.38/9.59          | ~ (v1_relat_1 @ X0))),
% 9.38/9.59      inference('demod', [status(thm)], ['67', '75'])).
% 9.38/9.59  thf('77', plain,
% 9.38/9.59      ((~ (r1_tarski @ sk_B_1 @ sk_B_1)
% 9.38/9.59        | ~ (v1_relat_1 @ sk_D)
% 9.38/9.59        | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C)))),
% 9.38/9.59      inference('sup-', [status(thm)], ['45', '76'])).
% 9.38/9.59  thf(d10_xboole_0, axiom,
% 9.38/9.59    (![A:$i,B:$i]:
% 9.38/9.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.38/9.59  thf('78', plain,
% 9.38/9.59      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 9.38/9.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.38/9.59  thf('79', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 9.38/9.59      inference('simplify', [status(thm)], ['78'])).
% 9.38/9.59  thf('80', plain, ((v1_relat_1 @ sk_D)),
% 9.38/9.59      inference('demod', [status(thm)], ['39', '40'])).
% 9.38/9.59  thf('81', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 9.38/9.59      inference('demod', [status(thm)], ['77', '79', '80'])).
% 9.38/9.59  thf('82', plain,
% 9.38/9.59      (![X37 : $i, X38 : $i]:
% 9.38/9.59         (((k2_relat_1 @ X38) != (X37))
% 9.38/9.59          | (v2_funct_2 @ X38 @ X37)
% 9.38/9.59          | ~ (v5_relat_1 @ X38 @ X37)
% 9.38/9.59          | ~ (v1_relat_1 @ X38))),
% 9.38/9.59      inference('cnf', [status(esa)], [d3_funct_2])).
% 9.38/9.59  thf('83', plain,
% 9.38/9.59      (![X38 : $i]:
% 9.38/9.59         (~ (v1_relat_1 @ X38)
% 9.38/9.59          | ~ (v5_relat_1 @ X38 @ (k2_relat_1 @ X38))
% 9.38/9.59          | (v2_funct_2 @ X38 @ (k2_relat_1 @ X38)))),
% 9.38/9.59      inference('simplify', [status(thm)], ['82'])).
% 9.38/9.59  thf('84', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 9.38/9.59      inference('simplify', [status(thm)], ['78'])).
% 9.38/9.59  thf(d19_relat_1, axiom,
% 9.38/9.59    (![A:$i,B:$i]:
% 9.38/9.59     ( ( v1_relat_1 @ B ) =>
% 9.38/9.59       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 9.38/9.59  thf('85', plain,
% 9.38/9.59      (![X12 : $i, X13 : $i]:
% 9.38/9.59         (~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 9.38/9.59          | (v5_relat_1 @ X12 @ X13)
% 9.38/9.59          | ~ (v1_relat_1 @ X12))),
% 9.38/9.59      inference('cnf', [status(esa)], [d19_relat_1])).
% 9.38/9.59  thf('86', plain,
% 9.38/9.59      (![X0 : $i]:
% 9.38/9.59         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 9.38/9.59      inference('sup-', [status(thm)], ['84', '85'])).
% 9.38/9.59  thf('87', plain,
% 9.38/9.59      (![X38 : $i]:
% 9.38/9.59         ((v2_funct_2 @ X38 @ (k2_relat_1 @ X38)) | ~ (v1_relat_1 @ X38))),
% 9.38/9.59      inference('clc', [status(thm)], ['83', '86'])).
% 9.38/9.59  thf('88', plain,
% 9.38/9.59      (((v2_funct_2 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_C)
% 9.38/9.59        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 9.38/9.59      inference('sup+', [status(thm)], ['81', '87'])).
% 9.38/9.59  thf('89', plain,
% 9.38/9.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf('90', plain,
% 9.38/9.59      ((m1_subset_1 @ sk_D @ 
% 9.38/9.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B_1)))),
% 9.38/9.59      inference('demod', [status(thm)], ['23', '24'])).
% 9.38/9.59  thf(dt_k1_partfun1, axiom,
% 9.38/9.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 9.38/9.59     ( ( ( v1_funct_1 @ E ) & 
% 9.38/9.59         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 9.38/9.59         ( v1_funct_1 @ F ) & 
% 9.38/9.59         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 9.38/9.59       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 9.38/9.59         ( m1_subset_1 @
% 9.38/9.59           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 9.38/9.59           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 9.38/9.59  thf('91', plain,
% 9.38/9.59      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 9.38/9.59         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 9.38/9.59          | ~ (v1_funct_1 @ X39)
% 9.38/9.59          | ~ (v1_funct_1 @ X42)
% 9.38/9.59          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 9.38/9.59          | (m1_subset_1 @ (k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42) @ 
% 9.38/9.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X44))))),
% 9.38/9.59      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 9.38/9.59  thf('92', plain,
% 9.38/9.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.38/9.59         ((m1_subset_1 @ 
% 9.38/9.59           (k1_partfun1 @ (k1_relat_1 @ sk_D) @ sk_B_1 @ X2 @ X0 @ sk_D @ X1) @ 
% 9.38/9.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)))
% 9.38/9.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 9.38/9.59          | ~ (v1_funct_1 @ X1)
% 9.38/9.59          | ~ (v1_funct_1 @ sk_D))),
% 9.38/9.59      inference('sup-', [status(thm)], ['90', '91'])).
% 9.38/9.59  thf('93', plain, ((v1_funct_1 @ sk_D)),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf('94', plain,
% 9.38/9.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.38/9.59         ((m1_subset_1 @ 
% 9.38/9.59           (k1_partfun1 @ (k1_relat_1 @ sk_D) @ sk_B_1 @ X2 @ X0 @ sk_D @ X1) @ 
% 9.38/9.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)))
% 9.38/9.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 9.38/9.59          | ~ (v1_funct_1 @ X1))),
% 9.38/9.59      inference('demod', [status(thm)], ['92', '93'])).
% 9.38/9.59  thf('95', plain,
% 9.38/9.59      ((~ (v1_funct_1 @ sk_E)
% 9.38/9.59        | (m1_subset_1 @ 
% 9.38/9.59           (k1_partfun1 @ (k1_relat_1 @ sk_D) @ sk_B_1 @ sk_B_1 @ sk_C @ 
% 9.38/9.59            sk_D @ sk_E) @ 
% 9.38/9.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C))))),
% 9.38/9.59      inference('sup-', [status(thm)], ['89', '94'])).
% 9.38/9.59  thf('96', plain, ((v1_funct_1 @ sk_E)),
% 9.38/9.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.38/9.59  thf('97', plain,
% 9.38/9.59      ((m1_subset_1 @ 
% 9.38/9.59        (k1_partfun1 @ (k1_relat_1 @ sk_D) @ sk_B_1 @ sk_B_1 @ sk_C @ sk_D @ 
% 9.38/9.59         sk_E) @ 
% 9.38/9.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))),
% 9.38/9.59      inference('demod', [status(thm)], ['95', '96'])).
% 9.38/9.59  thf(cc1_relset_1, axiom,
% 9.38/9.59    (![A:$i,B:$i,C:$i]:
% 9.38/9.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.38/9.59       ( v1_relat_1 @ C ) ))).
% 9.38/9.59  thf('98', plain,
% 9.38/9.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 9.38/9.59         ((v1_relat_1 @ X20)
% 9.38/9.59          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 9.38/9.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 9.38/9.59  thf('99', plain,
% 9.38/9.59      ((v1_relat_1 @ 
% 9.38/9.59        (k1_partfun1 @ (k1_relat_1 @ sk_D) @ sk_B_1 @ sk_B_1 @ sk_C @ sk_D @ 
% 9.38/9.59         sk_E))),
% 9.38/9.59      inference('sup-', [status(thm)], ['97', '98'])).
% 9.38/9.59  thf('100', plain,
% 9.38/9.59      (((k1_partfun1 @ (k1_relat_1 @ sk_D) @ sk_B_1 @ sk_B_1 @ sk_C @ sk_D @ 
% 9.38/9.59         sk_E) = (k5_relat_1 @ sk_D @ sk_E))),
% 9.38/9.59      inference('demod', [status(thm)], ['30', '31'])).
% 9.38/9.59  thf('101', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_E))),
% 9.38/9.59      inference('demod', [status(thm)], ['99', '100'])).
% 9.38/9.59  thf('102', plain, ((v2_funct_2 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_C)),
% 9.38/9.59      inference('demod', [status(thm)], ['88', '101'])).
% 9.38/9.59  thf('103', plain, ($false), inference('demod', [status(thm)], ['33', '102'])).
% 9.38/9.59  
% 9.38/9.59  % SZS output end Refutation
% 9.38/9.59  
% 9.38/9.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
