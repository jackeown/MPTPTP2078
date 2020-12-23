%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FY5voGgHcb

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:02 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 157 expanded)
%              Number of leaves         :   34 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :  692 (2068 expanded)
%              Number of equality atoms :   38 ( 101 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X48: $i] :
      ( ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X48 ) @ ( k2_relat_1 @ X48 ) ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k7_relset_1 @ X37 @ X38 @ X36 @ X39 )
        = ( k9_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X48: $i] :
      ( ( v1_funct_2 @ X48 @ ( k1_relat_1 @ X48 ) @ ( k2_relat_1 @ X48 ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('4',plain,(
    ! [X48: $i] :
      ( ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X48 ) @ ( k2_relat_1 @ X48 ) ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(t44_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r1_tarski @ ( k7_relset_1 @ A @ B @ D @ C ) @ B ) ) )).

thf('5',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( r1_tarski @ ( k7_relset_1 @ X49 @ X50 @ X51 @ X52 ) @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X49 @ X50 )
      | ~ ( v1_funct_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t44_funct_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_D @ ( k1_tarski @ sk_A ) @ sk_B ),
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

thf('14',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('18',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('19',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['15','22','25'])).

thf('27',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','26'])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['15','22','25'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k1_relat_1 @ X29 )
       != ( k1_tarski @ X28 ) )
      | ( ( k2_relat_1 @ X29 )
        = ( k1_tarski @ ( k1_funct_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference(eq_res,[status(thm)],['30'])).

thf('32',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','35'])).

thf('37',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['27','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['15','22','25'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k7_relset_1 @ X37 @ X38 @ X36 @ X39 )
        = ( k9_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['44','45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.16/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FY5voGgHcb
% 0.16/0.37  % Computer   : n024.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 15:26:51 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.23/0.38  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.49/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.70  % Solved by: fo/fo7.sh
% 0.49/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.70  % done 126 iterations in 0.219s
% 0.49/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.70  % SZS output start Refutation
% 0.49/0.70  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.49/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.49/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.49/0.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.49/0.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.49/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.70  thf(sk_D_type, type, sk_D: $i).
% 0.49/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.49/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.70  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.49/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.70  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.49/0.70  thf(t3_funct_2, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.70       ( ( v1_funct_1 @ A ) & 
% 0.49/0.70         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.49/0.70         ( m1_subset_1 @
% 0.49/0.70           A @ 
% 0.49/0.70           ( k1_zfmisc_1 @
% 0.49/0.70             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.49/0.70  thf('0', plain,
% 0.49/0.70      (![X48 : $i]:
% 0.49/0.70         ((m1_subset_1 @ X48 @ 
% 0.49/0.70           (k1_zfmisc_1 @ 
% 0.49/0.70            (k2_zfmisc_1 @ (k1_relat_1 @ X48) @ (k2_relat_1 @ X48))))
% 0.49/0.70          | ~ (v1_funct_1 @ X48)
% 0.49/0.70          | ~ (v1_relat_1 @ X48))),
% 0.49/0.70      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.49/0.70  thf(redefinition_k7_relset_1, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.70       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.49/0.70  thf('1', plain,
% 0.49/0.70      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.49/0.70          | ((k7_relset_1 @ X37 @ X38 @ X36 @ X39) = (k9_relat_1 @ X36 @ X39)))),
% 0.49/0.70      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.49/0.70  thf('2', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | ((k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1)
% 0.49/0.70              = (k9_relat_1 @ X0 @ X1)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['0', '1'])).
% 0.49/0.70  thf('3', plain,
% 0.49/0.70      (![X48 : $i]:
% 0.49/0.70         ((v1_funct_2 @ X48 @ (k1_relat_1 @ X48) @ (k2_relat_1 @ X48))
% 0.49/0.70          | ~ (v1_funct_1 @ X48)
% 0.49/0.70          | ~ (v1_relat_1 @ X48))),
% 0.49/0.70      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.49/0.70  thf('4', plain,
% 0.49/0.70      (![X48 : $i]:
% 0.49/0.70         ((m1_subset_1 @ X48 @ 
% 0.49/0.70           (k1_zfmisc_1 @ 
% 0.49/0.70            (k2_zfmisc_1 @ (k1_relat_1 @ X48) @ (k2_relat_1 @ X48))))
% 0.49/0.70          | ~ (v1_funct_1 @ X48)
% 0.49/0.70          | ~ (v1_relat_1 @ X48))),
% 0.49/0.70      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.49/0.70  thf(t44_funct_2, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.70     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.49/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.70       ( r1_tarski @ ( k7_relset_1 @ A @ B @ D @ C ) @ B ) ))).
% 0.49/0.70  thf('5', plain,
% 0.49/0.70      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.49/0.70         ((r1_tarski @ (k7_relset_1 @ X49 @ X50 @ X51 @ X52) @ X50)
% 0.49/0.70          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 0.49/0.70          | ~ (v1_funct_2 @ X51 @ X49 @ X50)
% 0.49/0.70          | ~ (v1_funct_1 @ X51))),
% 0.49/0.70      inference('cnf', [status(esa)], [t44_funct_2])).
% 0.49/0.70  thf('6', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.49/0.70          | (r1_tarski @ 
% 0.49/0.70             (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 0.49/0.70             (k2_relat_1 @ X0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['4', '5'])).
% 0.49/0.70  thf('7', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((r1_tarski @ 
% 0.49/0.70           (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 0.49/0.70           (k2_relat_1 @ X0))
% 0.49/0.70          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | ~ (v1_relat_1 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['6'])).
% 0.49/0.70  thf('8', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | (r1_tarski @ 
% 0.49/0.70             (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 0.49/0.70             (k2_relat_1 @ X0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['3', '7'])).
% 0.49/0.70  thf('9', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((r1_tarski @ 
% 0.49/0.70           (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 0.49/0.70           (k2_relat_1 @ X0))
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | ~ (v1_relat_1 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['8'])).
% 0.49/0.70  thf('10', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | ~ (v1_relat_1 @ X1)
% 0.49/0.70          | ~ (v1_relat_1 @ X1)
% 0.49/0.70          | ~ (v1_funct_1 @ X1))),
% 0.49/0.70      inference('sup+', [status(thm)], ['2', '9'])).
% 0.49/0.70  thf('11', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ X1)
% 0.49/0.70          | ~ (v1_funct_1 @ X1)
% 0.49/0.70          | (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1)))),
% 0.49/0.70      inference('simplify', [status(thm)], ['10'])).
% 0.49/0.70  thf(t64_funct_2, conjecture,
% 0.49/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.70     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.49/0.70         ( m1_subset_1 @
% 0.49/0.70           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.49/0.70       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.49/0.70         ( r1_tarski @
% 0.49/0.70           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.49/0.70           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.49/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.70    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.70        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.49/0.70            ( m1_subset_1 @
% 0.49/0.70              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.49/0.70          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.49/0.70            ( r1_tarski @
% 0.49/0.70              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.49/0.70              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.49/0.70    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.49/0.70  thf('12', plain,
% 0.49/0.70      (~ (r1_tarski @ 
% 0.49/0.70          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.49/0.70          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('13', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(d1_funct_2, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.49/0.70           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.49/0.70             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.49/0.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.49/0.70           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.49/0.70             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.49/0.70  thf(zf_stmt_1, axiom,
% 0.49/0.70    (![C:$i,B:$i,A:$i]:
% 0.49/0.70     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.49/0.70       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.49/0.70  thf('14', plain,
% 0.49/0.70      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.49/0.70         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 0.49/0.70          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 0.49/0.70          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.49/0.70  thf('15', plain,
% 0.49/0.70      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.49/0.70        | ((k1_tarski @ sk_A)
% 0.49/0.70            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['13', '14'])).
% 0.49/0.70  thf(zf_stmt_2, axiom,
% 0.49/0.70    (![B:$i,A:$i]:
% 0.49/0.70     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.49/0.70       ( zip_tseitin_0 @ B @ A ) ))).
% 0.49/0.70  thf('16', plain,
% 0.49/0.70      (![X40 : $i, X41 : $i]:
% 0.49/0.70         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.70  thf('17', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_D @ 
% 0.49/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.49/0.70  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.49/0.70  thf(zf_stmt_5, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.70       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.49/0.70         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.49/0.70           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.49/0.70             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.49/0.70  thf('18', plain,
% 0.49/0.70      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.49/0.70         (~ (zip_tseitin_0 @ X45 @ X46)
% 0.49/0.70          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 0.49/0.70          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.49/0.70  thf('19', plain,
% 0.49/0.70      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.49/0.71        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.49/0.71  thf('20', plain,
% 0.49/0.71      ((((sk_B) = (k1_xboole_0))
% 0.49/0.71        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['16', '19'])).
% 0.49/0.71  thf('21', plain, (((sk_B) != (k1_xboole_0))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('22', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.49/0.71      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.49/0.71  thf('23', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_D @ 
% 0.49/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf(redefinition_k1_relset_1, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i]:
% 0.49/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.71       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.49/0.71  thf('24', plain,
% 0.49/0.71      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.49/0.71         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 0.49/0.71          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.49/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.49/0.71  thf('25', plain,
% 0.49/0.71      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.49/0.71      inference('sup-', [status(thm)], ['23', '24'])).
% 0.49/0.71  thf('26', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.49/0.71      inference('demod', [status(thm)], ['15', '22', '25'])).
% 0.49/0.71  thf('27', plain,
% 0.49/0.71      (~ (r1_tarski @ 
% 0.49/0.71          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.49/0.71          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.49/0.71      inference('demod', [status(thm)], ['12', '26'])).
% 0.49/0.71  thf('28', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.49/0.71      inference('demod', [status(thm)], ['15', '22', '25'])).
% 0.49/0.71  thf(t14_funct_1, axiom,
% 0.49/0.71    (![A:$i,B:$i]:
% 0.49/0.71     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.71       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.49/0.71         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.49/0.71  thf('29', plain,
% 0.49/0.71      (![X28 : $i, X29 : $i]:
% 0.49/0.71         (((k1_relat_1 @ X29) != (k1_tarski @ X28))
% 0.49/0.71          | ((k2_relat_1 @ X29) = (k1_tarski @ (k1_funct_1 @ X29 @ X28)))
% 0.49/0.71          | ~ (v1_funct_1 @ X29)
% 0.49/0.71          | ~ (v1_relat_1 @ X29))),
% 0.49/0.71      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.49/0.71  thf('30', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.49/0.71          | ~ (v1_relat_1 @ X0)
% 0.49/0.71          | ~ (v1_funct_1 @ X0)
% 0.49/0.71          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.49/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.49/0.71  thf('31', plain,
% 0.49/0.71      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.49/0.71        | ~ (v1_funct_1 @ sk_D)
% 0.49/0.71        | ~ (v1_relat_1 @ sk_D))),
% 0.49/0.71      inference('eq_res', [status(thm)], ['30'])).
% 0.49/0.71  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('33', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_D @ 
% 0.49/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf(cc1_relset_1, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i]:
% 0.49/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.71       ( v1_relat_1 @ C ) ))).
% 0.49/0.71  thf('34', plain,
% 0.49/0.71      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.49/0.71         ((v1_relat_1 @ X30)
% 0.49/0.71          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.49/0.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.49/0.71  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 0.49/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.49/0.71  thf('36', plain,
% 0.49/0.71      (((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.49/0.71      inference('demod', [status(thm)], ['31', '32', '35'])).
% 0.49/0.71  thf('37', plain,
% 0.49/0.71      (~ (r1_tarski @ 
% 0.49/0.71          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.49/0.71          (k2_relat_1 @ sk_D))),
% 0.49/0.71      inference('demod', [status(thm)], ['27', '36'])).
% 0.49/0.71  thf('38', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_D @ 
% 0.49/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('39', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.49/0.71      inference('demod', [status(thm)], ['15', '22', '25'])).
% 0.49/0.71  thf('40', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_D @ 
% 0.49/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.49/0.71      inference('demod', [status(thm)], ['38', '39'])).
% 0.49/0.71  thf('41', plain,
% 0.49/0.71      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.49/0.71         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.49/0.71          | ((k7_relset_1 @ X37 @ X38 @ X36 @ X39) = (k9_relat_1 @ X36 @ X39)))),
% 0.49/0.71      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.49/0.71  thf('42', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.49/0.71           = (k9_relat_1 @ sk_D @ X0))),
% 0.49/0.71      inference('sup-', [status(thm)], ['40', '41'])).
% 0.49/0.71  thf('43', plain,
% 0.49/0.71      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.49/0.71      inference('demod', [status(thm)], ['37', '42'])).
% 0.49/0.71  thf('44', plain, ((~ (v1_funct_1 @ sk_D) | ~ (v1_relat_1 @ sk_D))),
% 0.49/0.71      inference('sup-', [status(thm)], ['11', '43'])).
% 0.49/0.71  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.49/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.49/0.71  thf('47', plain, ($false),
% 0.49/0.71      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.49/0.71  
% 0.49/0.71  % SZS output end Refutation
% 0.49/0.71  
% 0.49/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
