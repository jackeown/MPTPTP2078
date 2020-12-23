%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M8IImfn94U

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:35 EST 2020

% Result     : Theorem 20.05s
% Output     : Refutation 20.05s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 982 expanded)
%              Number of leaves         :   41 ( 294 expanded)
%              Depth                    :   23
%              Number of atoms          : 1777 (18703 expanded)
%              Number of equality atoms :  127 ( 913 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t38_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
            & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
            & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ C @ A )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
              & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
              & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ( ( k2_partfun1 @ X36 @ X37 @ X35 @ X38 )
        = ( k7_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['1','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X32 @ X33 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ sk_C @ sk_A ),
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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('18',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('19',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
      = sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X32 @ X33 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('50',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['48','51'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X39 ) @ X40 )
      | ( v1_funct_2 @ X39 @ ( k1_relat_1 @ X39 ) @ X40 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('56',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('58',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['54','55','58'])).

thf('60',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('62',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B != k1_xboole_0 )
      & ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,
    ( ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('70',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('72',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C )
      | ( k1_xboole_0 = sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('74',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('75',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('77',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ sk_C @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('82',plain,
    ( ( v4_relat_1 @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('83',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('84',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ( sk_D
        = ( k7_relat_1 @ sk_D @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('86',plain,
    ( ( sk_D
      = ( k7_relat_1 @ sk_D @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('88',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('89',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['77','86','87','90'])).

thf('92',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('93',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('94',plain,(
    ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['14','68','91','92','93'])).

thf('95',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['7','94'])).

thf('96',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('99',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('101',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('103',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X39 ) @ X40 )
      | ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X39 ) @ X40 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('105',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('107',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('110',plain,(
    v4_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('112',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('114',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('116',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['114','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('123',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('124',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['33','34'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['121','122','123','124'])).

thf('126',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('127',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('128',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('135',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_B = X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['133','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('139',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( X1 = sk_B )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['137','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = sk_B )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( k1_xboole_0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['126','142'])).

thf('144',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('145',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('147',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('148',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['145','148'])).

thf('150',plain,
    ( ( sk_D
      = ( k7_relat_1 @ sk_D @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('151',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('152',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('153',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['149','150','151','152'])).

thf('154',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['14','68','91','93','153','92'])).

thf('155',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['144','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['143','155'])).

thf('157',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('158',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('160',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['125','160'])).

thf('162',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['96','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('164',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X39 ) @ X40 )
      | ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X39 ) @ X40 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('167',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('168',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['162','168'])).

thf('170',plain,(
    $false ),
    inference(demod,[status(thm)],['95','169'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M8IImfn94U
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:39:03 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 20.05/20.32  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 20.05/20.32  % Solved by: fo/fo7.sh
% 20.05/20.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 20.05/20.32  % done 11783 iterations in 19.866s
% 20.05/20.32  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 20.05/20.32  % SZS output start Refutation
% 20.05/20.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 20.05/20.32  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 20.05/20.32  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 20.05/20.32  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 20.05/20.32  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 20.05/20.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 20.05/20.32  thf(sk_D_type, type, sk_D: $i).
% 20.05/20.32  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 20.05/20.32  thf(sk_C_type, type, sk_C: $i).
% 20.05/20.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 20.05/20.32  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 20.05/20.32  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 20.05/20.32  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 20.05/20.32  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 20.05/20.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 20.05/20.32  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 20.05/20.32  thf(sk_B_type, type, sk_B: $i).
% 20.05/20.32  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 20.05/20.32  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 20.05/20.32  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 20.05/20.32  thf(sk_A_type, type, sk_A: $i).
% 20.05/20.32  thf(t38_funct_2, conjecture,
% 20.05/20.32    (![A:$i,B:$i,C:$i,D:$i]:
% 20.05/20.32     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 20.05/20.32         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 20.05/20.32       ( ( r1_tarski @ C @ A ) =>
% 20.05/20.32         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 20.05/20.32           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 20.05/20.32             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 20.05/20.32             ( m1_subset_1 @
% 20.05/20.32               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 20.05/20.32               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 20.05/20.32  thf(zf_stmt_0, negated_conjecture,
% 20.05/20.32    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 20.05/20.32        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 20.05/20.32            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 20.05/20.32          ( ( r1_tarski @ C @ A ) =>
% 20.05/20.32            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 20.05/20.32              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 20.05/20.32                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 20.05/20.32                ( m1_subset_1 @
% 20.05/20.32                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 20.05/20.32                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 20.05/20.32    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 20.05/20.32  thf('0', plain,
% 20.05/20.32      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 20.05/20.32        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 20.05/20.32             sk_B)
% 20.05/20.32        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 20.05/20.32             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.05/20.32  thf('1', plain,
% 20.05/20.32      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 20.05/20.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 20.05/20.32         <= (~
% 20.05/20.32             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 20.05/20.32               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 20.05/20.32      inference('split', [status(esa)], ['0'])).
% 20.05/20.32  thf('2', plain,
% 20.05/20.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.05/20.32  thf(redefinition_k2_partfun1, axiom,
% 20.05/20.32    (![A:$i,B:$i,C:$i,D:$i]:
% 20.05/20.32     ( ( ( v1_funct_1 @ C ) & 
% 20.05/20.32         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 20.05/20.32       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 20.05/20.32  thf('3', plain,
% 20.05/20.32      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 20.05/20.32         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 20.05/20.32          | ~ (v1_funct_1 @ X35)
% 20.05/20.32          | ((k2_partfun1 @ X36 @ X37 @ X35 @ X38) = (k7_relat_1 @ X35 @ X38)))),
% 20.05/20.32      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 20.05/20.32  thf('4', plain,
% 20.05/20.32      (![X0 : $i]:
% 20.05/20.32         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 20.05/20.32          | ~ (v1_funct_1 @ sk_D))),
% 20.05/20.32      inference('sup-', [status(thm)], ['2', '3'])).
% 20.05/20.32  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.05/20.32  thf('6', plain,
% 20.05/20.32      (![X0 : $i]:
% 20.05/20.32         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 20.05/20.32      inference('demod', [status(thm)], ['4', '5'])).
% 20.05/20.32  thf('7', plain,
% 20.05/20.32      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 20.05/20.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 20.05/20.32         <= (~
% 20.05/20.32             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 20.05/20.32               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 20.05/20.32      inference('demod', [status(thm)], ['1', '6'])).
% 20.05/20.32  thf('8', plain,
% 20.05/20.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.05/20.32  thf(dt_k2_partfun1, axiom,
% 20.05/20.32    (![A:$i,B:$i,C:$i,D:$i]:
% 20.05/20.32     ( ( ( v1_funct_1 @ C ) & 
% 20.05/20.32         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 20.05/20.32       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 20.05/20.32         ( m1_subset_1 @
% 20.05/20.32           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 20.05/20.32           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 20.05/20.32  thf('9', plain,
% 20.05/20.32      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 20.05/20.32         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 20.05/20.32          | ~ (v1_funct_1 @ X31)
% 20.05/20.32          | (v1_funct_1 @ (k2_partfun1 @ X32 @ X33 @ X31 @ X34)))),
% 20.05/20.32      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 20.05/20.32  thf('10', plain,
% 20.05/20.32      (![X0 : $i]:
% 20.05/20.32         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 20.05/20.32          | ~ (v1_funct_1 @ sk_D))),
% 20.05/20.32      inference('sup-', [status(thm)], ['8', '9'])).
% 20.05/20.32  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.05/20.32  thf('12', plain,
% 20.05/20.32      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 20.05/20.32      inference('demod', [status(thm)], ['10', '11'])).
% 20.05/20.32  thf('13', plain,
% 20.05/20.32      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))
% 20.05/20.32         <= (~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))))),
% 20.05/20.32      inference('split', [status(esa)], ['0'])).
% 20.05/20.32  thf('14', plain,
% 20.05/20.32      (((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 20.05/20.32      inference('sup-', [status(thm)], ['12', '13'])).
% 20.05/20.32  thf('15', plain, ((r1_tarski @ sk_C @ sk_A)),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.05/20.32  thf(d1_funct_2, axiom,
% 20.05/20.32    (![A:$i,B:$i,C:$i]:
% 20.05/20.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.05/20.32       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 20.05/20.32           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 20.05/20.32             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 20.05/20.32         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 20.05/20.32           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 20.05/20.32             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 20.05/20.32  thf(zf_stmt_1, axiom,
% 20.05/20.32    (![B:$i,A:$i]:
% 20.05/20.32     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 20.05/20.32       ( zip_tseitin_0 @ B @ A ) ))).
% 20.05/20.32  thf('16', plain,
% 20.05/20.32      (![X23 : $i, X24 : $i]:
% 20.05/20.32         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_1])).
% 20.05/20.32  thf('17', plain,
% 20.05/20.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.05/20.32  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 20.05/20.32  thf(zf_stmt_3, axiom,
% 20.05/20.32    (![C:$i,B:$i,A:$i]:
% 20.05/20.32     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 20.05/20.32       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 20.05/20.32  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 20.05/20.32  thf(zf_stmt_5, axiom,
% 20.05/20.32    (![A:$i,B:$i,C:$i]:
% 20.05/20.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.05/20.32       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 20.05/20.32         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 20.05/20.32           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 20.05/20.32             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 20.05/20.32  thf('18', plain,
% 20.05/20.32      (![X28 : $i, X29 : $i, X30 : $i]:
% 20.05/20.32         (~ (zip_tseitin_0 @ X28 @ X29)
% 20.05/20.32          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 20.05/20.32          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_5])).
% 20.05/20.32  thf('19', plain,
% 20.05/20.32      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 20.05/20.32      inference('sup-', [status(thm)], ['17', '18'])).
% 20.05/20.32  thf('20', plain,
% 20.05/20.32      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 20.05/20.32      inference('sup-', [status(thm)], ['16', '19'])).
% 20.05/20.32  thf('21', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.05/20.32  thf('22', plain,
% 20.05/20.32      (![X25 : $i, X26 : $i, X27 : $i]:
% 20.05/20.32         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 20.05/20.32          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 20.05/20.32          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_3])).
% 20.05/20.32  thf('23', plain,
% 20.05/20.32      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 20.05/20.32        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 20.05/20.32      inference('sup-', [status(thm)], ['21', '22'])).
% 20.05/20.32  thf('24', plain,
% 20.05/20.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.05/20.32  thf(redefinition_k1_relset_1, axiom,
% 20.05/20.32    (![A:$i,B:$i,C:$i]:
% 20.05/20.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.05/20.32       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 20.05/20.32  thf('25', plain,
% 20.05/20.32      (![X20 : $i, X21 : $i, X22 : $i]:
% 20.05/20.32         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 20.05/20.32          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 20.05/20.32      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 20.05/20.32  thf('26', plain,
% 20.05/20.32      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 20.05/20.32      inference('sup-', [status(thm)], ['24', '25'])).
% 20.05/20.32  thf('27', plain,
% 20.05/20.32      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 20.05/20.32      inference('demod', [status(thm)], ['23', '26'])).
% 20.05/20.32  thf('28', plain,
% 20.05/20.32      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 20.05/20.32      inference('sup-', [status(thm)], ['20', '27'])).
% 20.05/20.32  thf(t91_relat_1, axiom,
% 20.05/20.32    (![A:$i,B:$i]:
% 20.05/20.32     ( ( v1_relat_1 @ B ) =>
% 20.05/20.32       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 20.05/20.32         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 20.05/20.32  thf('29', plain,
% 20.05/20.32      (![X12 : $i, X13 : $i]:
% 20.05/20.32         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 20.05/20.32          | ((k1_relat_1 @ (k7_relat_1 @ X13 @ X12)) = (X12))
% 20.05/20.32          | ~ (v1_relat_1 @ X13))),
% 20.05/20.32      inference('cnf', [status(esa)], [t91_relat_1])).
% 20.05/20.32  thf('30', plain,
% 20.05/20.32      (![X0 : $i]:
% 20.05/20.32         (~ (r1_tarski @ X0 @ sk_A)
% 20.05/20.32          | ((sk_B) = (k1_xboole_0))
% 20.05/20.32          | ~ (v1_relat_1 @ sk_D)
% 20.05/20.32          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 20.05/20.32      inference('sup-', [status(thm)], ['28', '29'])).
% 20.05/20.32  thf('31', plain,
% 20.05/20.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.05/20.32  thf(cc2_relat_1, axiom,
% 20.05/20.32    (![A:$i]:
% 20.05/20.32     ( ( v1_relat_1 @ A ) =>
% 20.05/20.32       ( ![B:$i]:
% 20.05/20.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 20.05/20.32  thf('32', plain,
% 20.05/20.32      (![X4 : $i, X5 : $i]:
% 20.05/20.32         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 20.05/20.32          | (v1_relat_1 @ X4)
% 20.05/20.32          | ~ (v1_relat_1 @ X5))),
% 20.05/20.32      inference('cnf', [status(esa)], [cc2_relat_1])).
% 20.05/20.32  thf('33', plain,
% 20.05/20.32      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 20.05/20.32      inference('sup-', [status(thm)], ['31', '32'])).
% 20.05/20.32  thf(fc6_relat_1, axiom,
% 20.05/20.32    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 20.05/20.32  thf('34', plain,
% 20.05/20.32      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 20.05/20.32      inference('cnf', [status(esa)], [fc6_relat_1])).
% 20.05/20.32  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 20.05/20.32      inference('demod', [status(thm)], ['33', '34'])).
% 20.05/20.32  thf('36', plain,
% 20.05/20.32      (![X0 : $i]:
% 20.05/20.32         (~ (r1_tarski @ X0 @ sk_A)
% 20.05/20.32          | ((sk_B) = (k1_xboole_0))
% 20.05/20.32          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 20.05/20.32      inference('demod', [status(thm)], ['30', '35'])).
% 20.05/20.32  thf('37', plain,
% 20.05/20.32      ((((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))
% 20.05/20.32        | ((sk_B) = (k1_xboole_0)))),
% 20.05/20.32      inference('sup-', [status(thm)], ['15', '36'])).
% 20.05/20.32  thf('38', plain,
% 20.05/20.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.05/20.32  thf('39', plain,
% 20.05/20.32      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 20.05/20.32         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 20.05/20.32          | ~ (v1_funct_1 @ X31)
% 20.05/20.32          | (m1_subset_1 @ (k2_partfun1 @ X32 @ X33 @ X31 @ X34) @ 
% 20.05/20.32             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 20.05/20.32      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 20.05/20.32  thf('40', plain,
% 20.05/20.32      (![X0 : $i]:
% 20.05/20.32         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 20.05/20.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 20.05/20.32          | ~ (v1_funct_1 @ sk_D))),
% 20.05/20.32      inference('sup-', [status(thm)], ['38', '39'])).
% 20.05/20.32  thf('41', plain, ((v1_funct_1 @ sk_D)),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.05/20.32  thf('42', plain,
% 20.05/20.32      (![X0 : $i]:
% 20.05/20.32         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 20.05/20.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.05/20.32      inference('demod', [status(thm)], ['40', '41'])).
% 20.05/20.32  thf('43', plain,
% 20.05/20.32      (![X0 : $i]:
% 20.05/20.32         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 20.05/20.32      inference('demod', [status(thm)], ['4', '5'])).
% 20.05/20.32  thf('44', plain,
% 20.05/20.32      (![X0 : $i]:
% 20.05/20.32         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 20.05/20.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.05/20.32      inference('demod', [status(thm)], ['42', '43'])).
% 20.05/20.32  thf(cc2_relset_1, axiom,
% 20.05/20.32    (![A:$i,B:$i,C:$i]:
% 20.05/20.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.05/20.32       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 20.05/20.32  thf('45', plain,
% 20.05/20.32      (![X17 : $i, X18 : $i, X19 : $i]:
% 20.05/20.32         ((v5_relat_1 @ X17 @ X19)
% 20.05/20.32          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 20.05/20.32      inference('cnf', [status(esa)], [cc2_relset_1])).
% 20.05/20.32  thf('46', plain,
% 20.05/20.32      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 20.05/20.32      inference('sup-', [status(thm)], ['44', '45'])).
% 20.05/20.32  thf(d19_relat_1, axiom,
% 20.05/20.32    (![A:$i,B:$i]:
% 20.05/20.32     ( ( v1_relat_1 @ B ) =>
% 20.05/20.32       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 20.05/20.32  thf('47', plain,
% 20.05/20.32      (![X6 : $i, X7 : $i]:
% 20.05/20.32         (~ (v5_relat_1 @ X6 @ X7)
% 20.05/20.32          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 20.05/20.32          | ~ (v1_relat_1 @ X6))),
% 20.05/20.32      inference('cnf', [status(esa)], [d19_relat_1])).
% 20.05/20.32  thf('48', plain,
% 20.05/20.32      (![X0 : $i]:
% 20.05/20.32         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 20.05/20.32          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 20.05/20.32      inference('sup-', [status(thm)], ['46', '47'])).
% 20.05/20.32  thf('49', plain,
% 20.05/20.32      (![X0 : $i]:
% 20.05/20.32         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 20.05/20.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.05/20.32      inference('demod', [status(thm)], ['42', '43'])).
% 20.05/20.32  thf(cc1_relset_1, axiom,
% 20.05/20.32    (![A:$i,B:$i,C:$i]:
% 20.05/20.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.05/20.32       ( v1_relat_1 @ C ) ))).
% 20.05/20.32  thf('50', plain,
% 20.05/20.32      (![X14 : $i, X15 : $i, X16 : $i]:
% 20.05/20.32         ((v1_relat_1 @ X14)
% 20.05/20.32          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 20.05/20.32      inference('cnf', [status(esa)], [cc1_relset_1])).
% 20.05/20.32  thf('51', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 20.05/20.32      inference('sup-', [status(thm)], ['49', '50'])).
% 20.05/20.32  thf('52', plain,
% 20.05/20.32      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 20.05/20.32      inference('demod', [status(thm)], ['48', '51'])).
% 20.05/20.32  thf(t4_funct_2, axiom,
% 20.05/20.32    (![A:$i,B:$i]:
% 20.05/20.32     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 20.05/20.32       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 20.05/20.32         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 20.05/20.32           ( m1_subset_1 @
% 20.05/20.32             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 20.05/20.32  thf('53', plain,
% 20.05/20.32      (![X39 : $i, X40 : $i]:
% 20.05/20.32         (~ (r1_tarski @ (k2_relat_1 @ X39) @ X40)
% 20.05/20.32          | (v1_funct_2 @ X39 @ (k1_relat_1 @ X39) @ X40)
% 20.05/20.32          | ~ (v1_funct_1 @ X39)
% 20.05/20.32          | ~ (v1_relat_1 @ X39))),
% 20.05/20.32      inference('cnf', [status(esa)], [t4_funct_2])).
% 20.05/20.32  thf('54', plain,
% 20.05/20.32      (![X0 : $i]:
% 20.05/20.32         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 20.05/20.32          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 20.05/20.32          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 20.05/20.32             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 20.05/20.32      inference('sup-', [status(thm)], ['52', '53'])).
% 20.05/20.32  thf('55', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 20.05/20.32      inference('sup-', [status(thm)], ['49', '50'])).
% 20.05/20.32  thf('56', plain,
% 20.05/20.32      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 20.05/20.32      inference('demod', [status(thm)], ['10', '11'])).
% 20.05/20.32  thf('57', plain,
% 20.05/20.32      (![X0 : $i]:
% 20.05/20.32         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 20.05/20.32      inference('demod', [status(thm)], ['4', '5'])).
% 20.05/20.32  thf('58', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 20.05/20.32      inference('demod', [status(thm)], ['56', '57'])).
% 20.05/20.32  thf('59', plain,
% 20.05/20.32      (![X0 : $i]:
% 20.05/20.32         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 20.05/20.32          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 20.05/20.32      inference('demod', [status(thm)], ['54', '55', '58'])).
% 20.05/20.32  thf('60', plain,
% 20.05/20.32      (((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 20.05/20.32        | ((sk_B) = (k1_xboole_0)))),
% 20.05/20.32      inference('sup+', [status(thm)], ['37', '59'])).
% 20.05/20.32  thf('61', plain,
% 20.05/20.32      (![X0 : $i]:
% 20.05/20.32         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 20.05/20.32      inference('demod', [status(thm)], ['4', '5'])).
% 20.05/20.32  thf('62', plain,
% 20.05/20.32      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))
% 20.05/20.32         <= (~
% 20.05/20.32             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 20.05/20.32               sk_B)))),
% 20.05/20.32      inference('split', [status(esa)], ['0'])).
% 20.05/20.32  thf('63', plain,
% 20.05/20.32      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))
% 20.05/20.32         <= (~
% 20.05/20.32             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 20.05/20.32               sk_B)))),
% 20.05/20.32      inference('sup-', [status(thm)], ['61', '62'])).
% 20.05/20.32  thf('64', plain,
% 20.05/20.32      ((((sk_B) = (k1_xboole_0)))
% 20.05/20.32         <= (~
% 20.05/20.32             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 20.05/20.32               sk_B)))),
% 20.05/20.32      inference('sup-', [status(thm)], ['60', '63'])).
% 20.05/20.32  thf('65', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.05/20.32  thf('66', plain,
% 20.05/20.32      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 20.05/20.32      inference('split', [status(esa)], ['65'])).
% 20.05/20.32  thf('67', plain,
% 20.05/20.32      ((((k1_xboole_0) != (k1_xboole_0)))
% 20.05/20.32         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 20.05/20.32             ~
% 20.05/20.32             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 20.05/20.32               sk_B)))),
% 20.05/20.32      inference('sup-', [status(thm)], ['64', '66'])).
% 20.05/20.32  thf('68', plain,
% 20.05/20.32      (((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)) | 
% 20.05/20.32       (((sk_B) = (k1_xboole_0)))),
% 20.05/20.32      inference('simplify', [status(thm)], ['67'])).
% 20.05/20.32  thf('69', plain,
% 20.05/20.32      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 20.05/20.32      inference('split', [status(esa)], ['65'])).
% 20.05/20.32  thf('70', plain, ((r1_tarski @ sk_C @ sk_A)),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.05/20.32  thf('71', plain,
% 20.05/20.32      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 20.05/20.32      inference('sup+', [status(thm)], ['69', '70'])).
% 20.05/20.32  thf(d10_xboole_0, axiom,
% 20.05/20.32    (![A:$i,B:$i]:
% 20.05/20.32     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 20.05/20.32  thf('72', plain,
% 20.05/20.32      (![X0 : $i, X2 : $i]:
% 20.05/20.32         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 20.05/20.32      inference('cnf', [status(esa)], [d10_xboole_0])).
% 20.05/20.32  thf('73', plain,
% 20.05/20.32      (((~ (r1_tarski @ k1_xboole_0 @ sk_C) | ((k1_xboole_0) = (sk_C))))
% 20.05/20.32         <= ((((sk_A) = (k1_xboole_0))))),
% 20.05/20.32      inference('sup-', [status(thm)], ['71', '72'])).
% 20.05/20.32  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 20.05/20.32  thf('74', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 20.05/20.32      inference('cnf', [status(esa)], [t2_xboole_1])).
% 20.05/20.32  thf('75', plain,
% 20.05/20.32      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 20.05/20.32      inference('demod', [status(thm)], ['73', '74'])).
% 20.05/20.32  thf('76', plain,
% 20.05/20.32      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))
% 20.05/20.32         <= (~
% 20.05/20.32             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 20.05/20.32               sk_B)))),
% 20.05/20.32      inference('sup-', [status(thm)], ['61', '62'])).
% 20.05/20.32  thf('77', plain,
% 20.05/20.32      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ sk_C @ sk_B))
% 20.05/20.32         <= (~
% 20.05/20.32             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 20.05/20.32               sk_B)) & 
% 20.05/20.32             (((sk_A) = (k1_xboole_0))))),
% 20.05/20.32      inference('sup-', [status(thm)], ['75', '76'])).
% 20.05/20.32  thf('78', plain,
% 20.05/20.32      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 20.05/20.32      inference('split', [status(esa)], ['65'])).
% 20.05/20.32  thf('79', plain,
% 20.05/20.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.05/20.32  thf('80', plain,
% 20.05/20.32      (((m1_subset_1 @ sk_D @ 
% 20.05/20.32         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 20.05/20.32         <= ((((sk_A) = (k1_xboole_0))))),
% 20.05/20.32      inference('sup+', [status(thm)], ['78', '79'])).
% 20.05/20.32  thf('81', plain,
% 20.05/20.32      (![X17 : $i, X18 : $i, X19 : $i]:
% 20.05/20.32         ((v4_relat_1 @ X17 @ X18)
% 20.05/20.32          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 20.05/20.32      inference('cnf', [status(esa)], [cc2_relset_1])).
% 20.05/20.32  thf('82', plain,
% 20.05/20.32      (((v4_relat_1 @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 20.05/20.32      inference('sup-', [status(thm)], ['80', '81'])).
% 20.05/20.32  thf(t209_relat_1, axiom,
% 20.05/20.32    (![A:$i,B:$i]:
% 20.05/20.32     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 20.05/20.32       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 20.05/20.32  thf('83', plain,
% 20.05/20.32      (![X10 : $i, X11 : $i]:
% 20.05/20.32         (((X10) = (k7_relat_1 @ X10 @ X11))
% 20.05/20.32          | ~ (v4_relat_1 @ X10 @ X11)
% 20.05/20.32          | ~ (v1_relat_1 @ X10))),
% 20.05/20.32      inference('cnf', [status(esa)], [t209_relat_1])).
% 20.05/20.32  thf('84', plain,
% 20.05/20.32      (((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ k1_xboole_0))))
% 20.05/20.32         <= ((((sk_A) = (k1_xboole_0))))),
% 20.05/20.32      inference('sup-', [status(thm)], ['82', '83'])).
% 20.05/20.32  thf('85', plain, ((v1_relat_1 @ sk_D)),
% 20.05/20.32      inference('demod', [status(thm)], ['33', '34'])).
% 20.05/20.32  thf('86', plain,
% 20.05/20.32      ((((sk_D) = (k7_relat_1 @ sk_D @ k1_xboole_0)))
% 20.05/20.32         <= ((((sk_A) = (k1_xboole_0))))),
% 20.05/20.32      inference('demod', [status(thm)], ['84', '85'])).
% 20.05/20.32  thf('87', plain,
% 20.05/20.32      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 20.05/20.32      inference('demod', [status(thm)], ['73', '74'])).
% 20.05/20.32  thf('88', plain,
% 20.05/20.32      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 20.05/20.32      inference('split', [status(esa)], ['65'])).
% 20.05/20.32  thf('89', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.05/20.32  thf('90', plain,
% 20.05/20.32      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 20.05/20.32         <= ((((sk_A) = (k1_xboole_0))))),
% 20.05/20.32      inference('sup+', [status(thm)], ['88', '89'])).
% 20.05/20.32  thf('91', plain,
% 20.05/20.32      (~ (((sk_A) = (k1_xboole_0))) | 
% 20.05/20.32       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 20.05/20.32      inference('demod', [status(thm)], ['77', '86', '87', '90'])).
% 20.05/20.32  thf('92', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 20.05/20.32      inference('split', [status(esa)], ['65'])).
% 20.05/20.32  thf('93', plain,
% 20.05/20.32      (~
% 20.05/20.32       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 20.05/20.32         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) | 
% 20.05/20.32       ~
% 20.05/20.32       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)) | 
% 20.05/20.32       ~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 20.05/20.32      inference('split', [status(esa)], ['0'])).
% 20.05/20.32  thf('94', plain,
% 20.05/20.32      (~
% 20.05/20.32       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 20.05/20.32         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 20.05/20.32      inference('sat_resolution*', [status(thm)],
% 20.05/20.32                ['14', '68', '91', '92', '93'])).
% 20.05/20.32  thf('95', plain,
% 20.05/20.32      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 20.05/20.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 20.05/20.32      inference('simpl_trail', [status(thm)], ['7', '94'])).
% 20.05/20.32  thf('96', plain, ((r1_tarski @ sk_C @ sk_A)),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.05/20.32  thf('97', plain,
% 20.05/20.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.05/20.32  thf('98', plain,
% 20.05/20.32      (![X17 : $i, X18 : $i, X19 : $i]:
% 20.05/20.32         ((v5_relat_1 @ X17 @ X19)
% 20.05/20.32          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 20.05/20.32      inference('cnf', [status(esa)], [cc2_relset_1])).
% 20.05/20.32  thf('99', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 20.05/20.32      inference('sup-', [status(thm)], ['97', '98'])).
% 20.05/20.32  thf('100', plain,
% 20.05/20.32      (![X6 : $i, X7 : $i]:
% 20.05/20.32         (~ (v5_relat_1 @ X6 @ X7)
% 20.05/20.32          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 20.05/20.32          | ~ (v1_relat_1 @ X6))),
% 20.05/20.32      inference('cnf', [status(esa)], [d19_relat_1])).
% 20.05/20.32  thf('101', plain,
% 20.05/20.32      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 20.05/20.32      inference('sup-', [status(thm)], ['99', '100'])).
% 20.05/20.32  thf('102', plain, ((v1_relat_1 @ sk_D)),
% 20.05/20.32      inference('demod', [status(thm)], ['33', '34'])).
% 20.05/20.32  thf('103', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 20.05/20.32      inference('demod', [status(thm)], ['101', '102'])).
% 20.05/20.32  thf('104', plain,
% 20.05/20.32      (![X39 : $i, X40 : $i]:
% 20.05/20.32         (~ (r1_tarski @ (k2_relat_1 @ X39) @ X40)
% 20.05/20.32          | (m1_subset_1 @ X39 @ 
% 20.05/20.32             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X39) @ X40)))
% 20.05/20.32          | ~ (v1_funct_1 @ X39)
% 20.05/20.32          | ~ (v1_relat_1 @ X39))),
% 20.05/20.32      inference('cnf', [status(esa)], [t4_funct_2])).
% 20.05/20.32  thf('105', plain,
% 20.05/20.32      ((~ (v1_relat_1 @ sk_D)
% 20.05/20.32        | ~ (v1_funct_1 @ sk_D)
% 20.05/20.32        | (m1_subset_1 @ sk_D @ 
% 20.05/20.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B))))),
% 20.05/20.32      inference('sup-', [status(thm)], ['103', '104'])).
% 20.05/20.32  thf('106', plain, ((v1_relat_1 @ sk_D)),
% 20.05/20.32      inference('demod', [status(thm)], ['33', '34'])).
% 20.05/20.32  thf('107', plain, ((v1_funct_1 @ sk_D)),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.05/20.32  thf('108', plain,
% 20.05/20.32      ((m1_subset_1 @ sk_D @ 
% 20.05/20.32        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 20.05/20.32      inference('demod', [status(thm)], ['105', '106', '107'])).
% 20.05/20.32  thf('109', plain,
% 20.05/20.32      (![X17 : $i, X18 : $i, X19 : $i]:
% 20.05/20.32         ((v4_relat_1 @ X17 @ X18)
% 20.05/20.32          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 20.05/20.32      inference('cnf', [status(esa)], [cc2_relset_1])).
% 20.05/20.32  thf('110', plain, ((v4_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))),
% 20.05/20.32      inference('sup-', [status(thm)], ['108', '109'])).
% 20.05/20.32  thf('111', plain,
% 20.05/20.32      (![X10 : $i, X11 : $i]:
% 20.05/20.32         (((X10) = (k7_relat_1 @ X10 @ X11))
% 20.05/20.32          | ~ (v4_relat_1 @ X10 @ X11)
% 20.05/20.32          | ~ (v1_relat_1 @ X10))),
% 20.05/20.32      inference('cnf', [status(esa)], [t209_relat_1])).
% 20.05/20.32  thf('112', plain,
% 20.05/20.32      ((~ (v1_relat_1 @ sk_D)
% 20.05/20.32        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))))),
% 20.05/20.32      inference('sup-', [status(thm)], ['110', '111'])).
% 20.05/20.32  thf('113', plain, ((v1_relat_1 @ sk_D)),
% 20.05/20.32      inference('demod', [status(thm)], ['33', '34'])).
% 20.05/20.32  thf('114', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 20.05/20.32      inference('demod', [status(thm)], ['112', '113'])).
% 20.05/20.32  thf('115', plain,
% 20.05/20.32      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 20.05/20.32      inference('cnf', [status(esa)], [d10_xboole_0])).
% 20.05/20.32  thf('116', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 20.05/20.32      inference('simplify', [status(thm)], ['115'])).
% 20.05/20.32  thf('117', plain,
% 20.05/20.32      (![X12 : $i, X13 : $i]:
% 20.05/20.32         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 20.05/20.32          | ((k1_relat_1 @ (k7_relat_1 @ X13 @ X12)) = (X12))
% 20.05/20.32          | ~ (v1_relat_1 @ X13))),
% 20.05/20.32      inference('cnf', [status(esa)], [t91_relat_1])).
% 20.05/20.32  thf('118', plain,
% 20.05/20.32      (![X0 : $i]:
% 20.05/20.32         (~ (v1_relat_1 @ X0)
% 20.05/20.32          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 20.05/20.32              = (k1_relat_1 @ X0)))),
% 20.05/20.32      inference('sup-', [status(thm)], ['116', '117'])).
% 20.05/20.32  thf('119', plain,
% 20.05/20.32      (![X12 : $i, X13 : $i]:
% 20.05/20.32         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 20.05/20.32          | ((k1_relat_1 @ (k7_relat_1 @ X13 @ X12)) = (X12))
% 20.05/20.32          | ~ (v1_relat_1 @ X13))),
% 20.05/20.32      inference('cnf', [status(esa)], [t91_relat_1])).
% 20.05/20.32  thf('120', plain,
% 20.05/20.32      (![X0 : $i, X1 : $i]:
% 20.05/20.32         (~ (r1_tarski @ X1 @ (k1_relat_1 @ X0))
% 20.05/20.32          | ~ (v1_relat_1 @ X0)
% 20.05/20.32          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 20.05/20.32          | ((k1_relat_1 @ 
% 20.05/20.32              (k7_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X1)) = (
% 20.05/20.32              X1)))),
% 20.05/20.32      inference('sup-', [status(thm)], ['118', '119'])).
% 20.05/20.32  thf('121', plain,
% 20.05/20.32      (![X0 : $i]:
% 20.05/20.32         (~ (v1_relat_1 @ sk_D)
% 20.05/20.32          | ((k1_relat_1 @ 
% 20.05/20.32              (k7_relat_1 @ (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)) @ X0))
% 20.05/20.32              = (X0))
% 20.05/20.32          | ~ (v1_relat_1 @ sk_D)
% 20.05/20.32          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_D)))),
% 20.05/20.32      inference('sup-', [status(thm)], ['114', '120'])).
% 20.05/20.32  thf('122', plain, ((v1_relat_1 @ sk_D)),
% 20.05/20.32      inference('demod', [status(thm)], ['33', '34'])).
% 20.05/20.32  thf('123', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 20.05/20.32      inference('demod', [status(thm)], ['112', '113'])).
% 20.05/20.32  thf('124', plain, ((v1_relat_1 @ sk_D)),
% 20.05/20.32      inference('demod', [status(thm)], ['33', '34'])).
% 20.05/20.32  thf('125', plain,
% 20.05/20.32      (![X0 : $i]:
% 20.05/20.32         (((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0))
% 20.05/20.32          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_D)))),
% 20.05/20.32      inference('demod', [status(thm)], ['121', '122', '123', '124'])).
% 20.05/20.32  thf('126', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 20.05/20.32      inference('cnf', [status(esa)], [t2_xboole_1])).
% 20.05/20.32  thf('127', plain,
% 20.05/20.32      (![X23 : $i, X24 : $i]:
% 20.05/20.32         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 20.05/20.32      inference('cnf', [status(esa)], [zf_stmt_1])).
% 20.05/20.32  thf('128', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 20.05/20.32      inference('cnf', [status(esa)], [t2_xboole_1])).
% 20.05/20.32  thf('129', plain,
% 20.05/20.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.05/20.32         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 20.05/20.32      inference('sup+', [status(thm)], ['127', '128'])).
% 20.05/20.32  thf('130', plain,
% 20.05/20.32      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 20.05/20.32      inference('sup-', [status(thm)], ['17', '18'])).
% 20.05/20.33  thf('131', plain,
% 20.05/20.33      (![X0 : $i]:
% 20.05/20.33         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 20.05/20.33      inference('sup-', [status(thm)], ['129', '130'])).
% 20.05/20.33  thf('132', plain,
% 20.05/20.33      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 20.05/20.33      inference('demod', [status(thm)], ['23', '26'])).
% 20.05/20.33  thf('133', plain,
% 20.05/20.33      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 20.05/20.33      inference('sup-', [status(thm)], ['131', '132'])).
% 20.05/20.33  thf('134', plain,
% 20.05/20.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.05/20.33         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 20.05/20.33      inference('sup+', [status(thm)], ['127', '128'])).
% 20.05/20.33  thf('135', plain,
% 20.05/20.33      (![X0 : $i, X2 : $i]:
% 20.05/20.33         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 20.05/20.33      inference('cnf', [status(esa)], [d10_xboole_0])).
% 20.05/20.33  thf('136', plain,
% 20.05/20.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.05/20.33         ((zip_tseitin_0 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 20.05/20.33      inference('sup-', [status(thm)], ['134', '135'])).
% 20.05/20.33  thf('137', plain,
% 20.05/20.33      (![X0 : $i, X1 : $i]:
% 20.05/20.33         (((sk_A) = (k1_relat_1 @ sk_D))
% 20.05/20.33          | ((sk_B) = (X0))
% 20.05/20.33          | (zip_tseitin_0 @ X0 @ X1))),
% 20.05/20.33      inference('sup-', [status(thm)], ['133', '136'])).
% 20.05/20.33  thf('138', plain,
% 20.05/20.33      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 20.05/20.33      inference('sup-', [status(thm)], ['131', '132'])).
% 20.05/20.33  thf('139', plain,
% 20.05/20.33      (![X0 : $i, X2 : $i]:
% 20.05/20.33         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 20.05/20.33      inference('cnf', [status(esa)], [d10_xboole_0])).
% 20.05/20.33  thf('140', plain,
% 20.05/20.33      (![X0 : $i]:
% 20.05/20.33         (((sk_A) = (k1_relat_1 @ sk_D))
% 20.05/20.33          | ~ (r1_tarski @ X0 @ sk_B)
% 20.05/20.33          | ((X0) = (sk_B)))),
% 20.05/20.33      inference('sup-', [status(thm)], ['138', '139'])).
% 20.05/20.33  thf('141', plain,
% 20.05/20.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.05/20.33         (~ (r1_tarski @ X1 @ X0)
% 20.05/20.33          | (zip_tseitin_0 @ X0 @ X2)
% 20.05/20.33          | ((sk_A) = (k1_relat_1 @ sk_D))
% 20.05/20.33          | ((X1) = (sk_B))
% 20.05/20.33          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 20.05/20.33      inference('sup-', [status(thm)], ['137', '140'])).
% 20.05/20.33  thf('142', plain,
% 20.05/20.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.05/20.33         (((X1) = (sk_B))
% 20.05/20.33          | ((sk_A) = (k1_relat_1 @ sk_D))
% 20.05/20.33          | (zip_tseitin_0 @ X0 @ X2)
% 20.05/20.33          | ~ (r1_tarski @ X1 @ X0))),
% 20.05/20.33      inference('simplify', [status(thm)], ['141'])).
% 20.05/20.33  thf('143', plain,
% 20.05/20.33      (![X0 : $i, X1 : $i]:
% 20.05/20.33         ((zip_tseitin_0 @ X0 @ X1)
% 20.05/20.33          | ((sk_A) = (k1_relat_1 @ sk_D))
% 20.05/20.33          | ((k1_xboole_0) = (sk_B)))),
% 20.05/20.33      inference('sup-', [status(thm)], ['126', '142'])).
% 20.05/20.33  thf('144', plain,
% 20.05/20.33      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 20.05/20.33      inference('split', [status(esa)], ['65'])).
% 20.05/20.33  thf('145', plain,
% 20.05/20.33      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 20.05/20.33      inference('demod', [status(thm)], ['73', '74'])).
% 20.05/20.33  thf('146', plain,
% 20.05/20.33      (![X0 : $i]:
% 20.05/20.33         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 20.05/20.33      inference('demod', [status(thm)], ['4', '5'])).
% 20.05/20.33  thf('147', plain,
% 20.05/20.33      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 20.05/20.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 20.05/20.33         <= (~
% 20.05/20.33             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 20.05/20.33               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 20.05/20.33      inference('split', [status(esa)], ['0'])).
% 20.05/20.33  thf('148', plain,
% 20.05/20.33      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 20.05/20.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 20.05/20.33         <= (~
% 20.05/20.33             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 20.05/20.33               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 20.05/20.33      inference('sup-', [status(thm)], ['146', '147'])).
% 20.05/20.33  thf('149', plain,
% 20.05/20.33      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ k1_xboole_0) @ 
% 20.05/20.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 20.05/20.33         <= (~
% 20.05/20.33             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 20.05/20.33               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) & 
% 20.05/20.33             (((sk_A) = (k1_xboole_0))))),
% 20.05/20.33      inference('sup-', [status(thm)], ['145', '148'])).
% 20.05/20.33  thf('150', plain,
% 20.05/20.33      ((((sk_D) = (k7_relat_1 @ sk_D @ k1_xboole_0)))
% 20.05/20.33         <= ((((sk_A) = (k1_xboole_0))))),
% 20.05/20.33      inference('demod', [status(thm)], ['84', '85'])).
% 20.05/20.33  thf('151', plain,
% 20.05/20.33      ((((k1_xboole_0) = (sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 20.05/20.33      inference('demod', [status(thm)], ['73', '74'])).
% 20.05/20.33  thf('152', plain,
% 20.05/20.33      (((m1_subset_1 @ sk_D @ 
% 20.05/20.33         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 20.05/20.33         <= ((((sk_A) = (k1_xboole_0))))),
% 20.05/20.33      inference('sup+', [status(thm)], ['78', '79'])).
% 20.05/20.33  thf('153', plain,
% 20.05/20.33      (~ (((sk_A) = (k1_xboole_0))) | 
% 20.05/20.33       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 20.05/20.33         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 20.05/20.33      inference('demod', [status(thm)], ['149', '150', '151', '152'])).
% 20.05/20.33  thf('154', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 20.05/20.33      inference('sat_resolution*', [status(thm)],
% 20.05/20.33                ['14', '68', '91', '93', '153', '92'])).
% 20.05/20.33  thf('155', plain, (((sk_B) != (k1_xboole_0))),
% 20.05/20.33      inference('simpl_trail', [status(thm)], ['144', '154'])).
% 20.05/20.33  thf('156', plain,
% 20.05/20.33      (![X0 : $i, X1 : $i]:
% 20.05/20.33         ((zip_tseitin_0 @ X0 @ X1) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 20.05/20.33      inference('simplify_reflect-', [status(thm)], ['143', '155'])).
% 20.05/20.33  thf('157', plain,
% 20.05/20.33      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 20.05/20.33      inference('sup-', [status(thm)], ['17', '18'])).
% 20.05/20.33  thf('158', plain,
% 20.05/20.33      ((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 20.05/20.33      inference('sup-', [status(thm)], ['156', '157'])).
% 20.05/20.33  thf('159', plain,
% 20.05/20.33      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 20.05/20.33      inference('demod', [status(thm)], ['23', '26'])).
% 20.05/20.33  thf('160', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 20.05/20.33      inference('clc', [status(thm)], ['158', '159'])).
% 20.05/20.33  thf('161', plain,
% 20.05/20.33      (![X0 : $i]:
% 20.05/20.33         (((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0))
% 20.05/20.33          | ~ (r1_tarski @ X0 @ sk_A))),
% 20.05/20.33      inference('demod', [status(thm)], ['125', '160'])).
% 20.05/20.33  thf('162', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 20.05/20.33      inference('sup-', [status(thm)], ['96', '161'])).
% 20.05/20.33  thf('163', plain,
% 20.05/20.33      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 20.05/20.33      inference('demod', [status(thm)], ['48', '51'])).
% 20.05/20.33  thf('164', plain,
% 20.05/20.33      (![X39 : $i, X40 : $i]:
% 20.05/20.33         (~ (r1_tarski @ (k2_relat_1 @ X39) @ X40)
% 20.05/20.33          | (m1_subset_1 @ X39 @ 
% 20.05/20.33             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X39) @ X40)))
% 20.05/20.33          | ~ (v1_funct_1 @ X39)
% 20.05/20.33          | ~ (v1_relat_1 @ X39))),
% 20.05/20.33      inference('cnf', [status(esa)], [t4_funct_2])).
% 20.05/20.33  thf('165', plain,
% 20.05/20.33      (![X0 : $i]:
% 20.05/20.33         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 20.05/20.33          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 20.05/20.33          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 20.05/20.33             (k1_zfmisc_1 @ 
% 20.05/20.33              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))))),
% 20.05/20.33      inference('sup-', [status(thm)], ['163', '164'])).
% 20.05/20.33  thf('166', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 20.05/20.33      inference('sup-', [status(thm)], ['49', '50'])).
% 20.05/20.33  thf('167', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 20.05/20.33      inference('demod', [status(thm)], ['56', '57'])).
% 20.05/20.33  thf('168', plain,
% 20.05/20.33      (![X0 : $i]:
% 20.05/20.33         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 20.05/20.33          (k1_zfmisc_1 @ 
% 20.05/20.33           (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)))),
% 20.05/20.33      inference('demod', [status(thm)], ['165', '166', '167'])).
% 20.05/20.33  thf('169', plain,
% 20.05/20.33      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 20.05/20.33        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 20.05/20.33      inference('sup+', [status(thm)], ['162', '168'])).
% 20.05/20.33  thf('170', plain, ($false), inference('demod', [status(thm)], ['95', '169'])).
% 20.05/20.33  
% 20.05/20.33  % SZS output end Refutation
% 20.05/20.33  
% 20.16/20.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
