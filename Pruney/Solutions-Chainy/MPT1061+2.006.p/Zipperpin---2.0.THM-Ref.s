%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MB9ZZqqYi3

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:53 EST 2020

% Result     : Theorem 27.13s
% Output     : Refutation 27.13s
% Verified   : 
% Statistics : Number of formulae       :  191 (3701 expanded)
%              Number of leaves         :   50 (1111 expanded)
%              Depth                    :   19
%              Number of atoms          : 1449 (69479 expanded)
%              Number of equality atoms :   83 (1257 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(t178_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ~ ( v1_xboole_0 @ D )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ A @ D )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) )
         => ( ( ( r1_tarski @ B @ A )
              & ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) )
           => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) )
              & ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C )
              & ( m1_subset_1 @ ( k2_partfun1 @ A @ D @ E @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ~ ( v1_xboole_0 @ D )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ A @ D )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) )
           => ( ( ( r1_tarski @ B @ A )
                & ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) )
             => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) )
                & ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C )
                & ( m1_subset_1 @ ( k2_partfun1 @ A @ D @ E @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t178_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ( ( k2_partfun1 @ X52 @ X53 @ X51 @ X54 )
        = ( k7_relat_1 @ X51 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X48 @ X49 @ X47 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('15',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','5','12','13','14'])).

thf('16',plain,(
    r1_tarski @ ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('18',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k7_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k9_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_E @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['16','19'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X36 ) @ X37 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ X38 )
      | ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X48 @ X49 @ X47 @ X50 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('35',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_D ),
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

thf('39',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('40',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,
    ( ( k1_relset_1 @ sk_A @ sk_D @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('45',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
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

thf('49',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('50',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    zip_tseitin_1 @ sk_E @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['44','53'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('55',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('58',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('60',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('61',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('63',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['37','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['59','60'])).

thf('65',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','36','63','64'])).

thf('66',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['15','65'])).

thf('67',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('68',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','36','63','64'])).

thf('69',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('70',plain,
    ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','36','63','64'])).

thf('73',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('74',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['37','62'])).

thf('76',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41
       != ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('78',plain,
    ( ( sk_B != sk_B )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['15','65'])).

thf('81',plain,(
    ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','81'])).

thf('83',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','82'])).

thf('84',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','36','63','64'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('85',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('86',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('88',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_C )
      = ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','81'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('90',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('91',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('92',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('93',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','81'])).

thf('94',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('95',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['88','89','91','92','93','94'])).

thf('96',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','95'])).

thf('97',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['37','62'])).

thf('98',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k1_relset_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ ( k7_relat_1 @ sk_E @ sk_B ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup+',[status(thm)],['97','102'])).

thf('104',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['37','62'])).

thf('105',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('106',plain,
    ( ( k1_relset_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['88','89','91','92','93','94'])).

thf('108',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['88','89','91','92','93','94'])).

thf('109',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('110',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('111',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('115',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('116',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('117',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('120',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('122',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['118','122'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('124',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('125',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','125'])).

thf('127',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['106','107','108','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','125'])).

thf('129',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41
       != ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X40 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('133',plain,(
    ! [X39: $i] :
      ( zip_tseitin_0 @ X39 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('135',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['133','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['131','137'])).

thf('139',plain,(
    $false ),
    inference(demod,[status(thm)],['96','127','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MB9ZZqqYi3
% 0.15/0.34  % Computer   : n025.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:54:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 27.13/27.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 27.13/27.34  % Solved by: fo/fo7.sh
% 27.13/27.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 27.13/27.34  % done 13532 iterations in 26.877s
% 27.13/27.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 27.13/27.34  % SZS output start Refutation
% 27.13/27.34  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 27.13/27.34  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 27.13/27.34  thf(sk_C_type, type, sk_C: $i).
% 27.13/27.34  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 27.13/27.34  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 27.13/27.34  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 27.13/27.34  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 27.13/27.34  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 27.13/27.34  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 27.13/27.34  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 27.13/27.34  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 27.13/27.34  thf(sk_E_type, type, sk_E: $i).
% 27.13/27.34  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 27.13/27.34  thf(sk_D_type, type, sk_D: $i).
% 27.13/27.34  thf(sk_B_type, type, sk_B: $i).
% 27.13/27.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 27.13/27.34  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 27.13/27.34  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 27.13/27.34  thf(sk_A_type, type, sk_A: $i).
% 27.13/27.34  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 27.13/27.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 27.13/27.34  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 27.13/27.34  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 27.13/27.34  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 27.13/27.34  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 27.13/27.34  thf(t178_funct_2, conjecture,
% 27.13/27.34    (![A:$i,B:$i,C:$i,D:$i]:
% 27.13/27.34     ( ( ~( v1_xboole_0 @ D ) ) =>
% 27.13/27.34       ( ![E:$i]:
% 27.13/27.34         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 27.13/27.34             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 27.13/27.34           ( ( ( r1_tarski @ B @ A ) & 
% 27.13/27.34               ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 27.13/27.34             ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 27.13/27.34               ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 27.13/27.34               ( m1_subset_1 @
% 27.13/27.34                 ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 27.13/27.34                 ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ))).
% 27.13/27.34  thf(zf_stmt_0, negated_conjecture,
% 27.13/27.34    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 27.13/27.34        ( ( ~( v1_xboole_0 @ D ) ) =>
% 27.13/27.34          ( ![E:$i]:
% 27.13/27.34            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 27.13/27.34                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 27.13/27.34              ( ( ( r1_tarski @ B @ A ) & 
% 27.13/27.34                  ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 27.13/27.34                ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 27.13/27.34                  ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 27.13/27.34                  ( m1_subset_1 @
% 27.13/27.34                    ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 27.13/27.34                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ) )),
% 27.13/27.34    inference('cnf.neg', [status(esa)], [t178_funct_2])).
% 27.13/27.34  thf('0', plain,
% 27.13/27.34      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B))
% 27.13/27.34        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 27.13/27.34             sk_C)
% 27.13/27.34        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 27.13/27.34             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.13/27.34  thf('1', plain,
% 27.13/27.34      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.13/27.34  thf(redefinition_k2_partfun1, axiom,
% 27.13/27.34    (![A:$i,B:$i,C:$i,D:$i]:
% 27.13/27.34     ( ( ( v1_funct_1 @ C ) & 
% 27.13/27.34         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 27.13/27.34       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 27.13/27.34  thf('2', plain,
% 27.13/27.34      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 27.13/27.34         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 27.13/27.34          | ~ (v1_funct_1 @ X51)
% 27.13/27.34          | ((k2_partfun1 @ X52 @ X53 @ X51 @ X54) = (k7_relat_1 @ X51 @ X54)))),
% 27.13/27.34      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 27.13/27.34  thf('3', plain,
% 27.13/27.34      (![X0 : $i]:
% 27.13/27.34         (((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 27.13/27.34          | ~ (v1_funct_1 @ sk_E))),
% 27.13/27.34      inference('sup-', [status(thm)], ['1', '2'])).
% 27.13/27.34  thf('4', plain, ((v1_funct_1 @ sk_E)),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.13/27.34  thf('5', plain,
% 27.13/27.34      (![X0 : $i]:
% 27.13/27.34         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 27.13/27.34      inference('demod', [status(thm)], ['3', '4'])).
% 27.13/27.34  thf('6', plain,
% 27.13/27.34      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.13/27.34  thf(dt_k2_partfun1, axiom,
% 27.13/27.34    (![A:$i,B:$i,C:$i,D:$i]:
% 27.13/27.34     ( ( ( v1_funct_1 @ C ) & 
% 27.13/27.34         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 27.13/27.34       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 27.13/27.34         ( m1_subset_1 @
% 27.13/27.34           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 27.13/27.34           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 27.13/27.34  thf('7', plain,
% 27.13/27.34      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 27.13/27.34         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 27.13/27.34          | ~ (v1_funct_1 @ X47)
% 27.13/27.34          | (v1_funct_1 @ (k2_partfun1 @ X48 @ X49 @ X47 @ X50)))),
% 27.13/27.34      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 27.13/27.34  thf('8', plain,
% 27.13/27.34      (![X0 : $i]:
% 27.13/27.34         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))
% 27.13/27.34          | ~ (v1_funct_1 @ sk_E))),
% 27.13/27.34      inference('sup-', [status(thm)], ['6', '7'])).
% 27.13/27.34  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.13/27.34  thf('10', plain,
% 27.13/27.34      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 27.13/27.34      inference('demod', [status(thm)], ['8', '9'])).
% 27.13/27.34  thf('11', plain,
% 27.13/27.34      (![X0 : $i]:
% 27.13/27.34         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 27.13/27.34      inference('demod', [status(thm)], ['3', '4'])).
% 27.13/27.34  thf('12', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 27.13/27.34      inference('demod', [status(thm)], ['10', '11'])).
% 27.13/27.34  thf('13', plain,
% 27.13/27.34      (![X0 : $i]:
% 27.13/27.34         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 27.13/27.34      inference('demod', [status(thm)], ['3', '4'])).
% 27.13/27.34  thf('14', plain,
% 27.13/27.34      (![X0 : $i]:
% 27.13/27.34         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 27.13/27.34      inference('demod', [status(thm)], ['3', '4'])).
% 27.13/27.34  thf('15', plain,
% 27.13/27.34      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 27.13/27.34        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 27.13/27.34             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 27.13/27.34      inference('demod', [status(thm)], ['0', '5', '12', '13', '14'])).
% 27.13/27.34  thf('16', plain,
% 27.13/27.34      ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_C)),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.13/27.34  thf('17', plain,
% 27.13/27.34      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.13/27.34  thf(redefinition_k7_relset_1, axiom,
% 27.13/27.34    (![A:$i,B:$i,C:$i,D:$i]:
% 27.13/27.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 27.13/27.34       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 27.13/27.34  thf('18', plain,
% 27.13/27.34      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 27.13/27.34         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 27.13/27.34          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 27.13/27.34      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 27.13/27.34  thf('19', plain,
% 27.13/27.34      (![X0 : $i]:
% 27.13/27.34         ((k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0) = (k9_relat_1 @ sk_E @ X0))),
% 27.13/27.34      inference('sup-', [status(thm)], ['17', '18'])).
% 27.13/27.34  thf('20', plain, ((r1_tarski @ (k9_relat_1 @ sk_E @ sk_B) @ sk_C)),
% 27.13/27.34      inference('demod', [status(thm)], ['16', '19'])).
% 27.13/27.34  thf(t148_relat_1, axiom,
% 27.13/27.34    (![A:$i,B:$i]:
% 27.13/27.34     ( ( v1_relat_1 @ B ) =>
% 27.13/27.34       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 27.13/27.34  thf('21', plain,
% 27.13/27.34      (![X17 : $i, X18 : $i]:
% 27.13/27.34         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 27.13/27.34          | ~ (v1_relat_1 @ X17))),
% 27.13/27.34      inference('cnf', [status(esa)], [t148_relat_1])).
% 27.13/27.34  thf(d10_xboole_0, axiom,
% 27.13/27.34    (![A:$i,B:$i]:
% 27.13/27.34     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 27.13/27.34  thf('22', plain,
% 27.13/27.34      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 27.13/27.34      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.13/27.34  thf('23', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 27.13/27.34      inference('simplify', [status(thm)], ['22'])).
% 27.13/27.34  thf(t11_relset_1, axiom,
% 27.13/27.34    (![A:$i,B:$i,C:$i]:
% 27.13/27.34     ( ( v1_relat_1 @ C ) =>
% 27.13/27.34       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 27.13/27.34           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 27.13/27.34         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 27.13/27.34  thf('24', plain,
% 27.13/27.34      (![X36 : $i, X37 : $i, X38 : $i]:
% 27.13/27.34         (~ (r1_tarski @ (k1_relat_1 @ X36) @ X37)
% 27.13/27.34          | ~ (r1_tarski @ (k2_relat_1 @ X36) @ X38)
% 27.13/27.34          | (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 27.13/27.34          | ~ (v1_relat_1 @ X36))),
% 27.13/27.34      inference('cnf', [status(esa)], [t11_relset_1])).
% 27.13/27.34  thf('25', plain,
% 27.13/27.34      (![X0 : $i, X1 : $i]:
% 27.13/27.34         (~ (v1_relat_1 @ X0)
% 27.13/27.34          | (m1_subset_1 @ X0 @ 
% 27.13/27.34             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 27.13/27.34          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 27.13/27.34      inference('sup-', [status(thm)], ['23', '24'])).
% 27.13/27.34  thf('26', plain,
% 27.13/27.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.13/27.34         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 27.13/27.34          | ~ (v1_relat_1 @ X1)
% 27.13/27.34          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 27.13/27.34             (k1_zfmisc_1 @ 
% 27.13/27.34              (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)))
% 27.13/27.34          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 27.13/27.34      inference('sup-', [status(thm)], ['21', '25'])).
% 27.13/27.34  thf('27', plain,
% 27.13/27.34      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 27.13/27.34        | (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 27.13/27.34           (k1_zfmisc_1 @ 
% 27.13/27.34            (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C)))
% 27.13/27.34        | ~ (v1_relat_1 @ sk_E))),
% 27.13/27.34      inference('sup-', [status(thm)], ['20', '26'])).
% 27.13/27.34  thf('28', plain,
% 27.13/27.34      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.13/27.34  thf('29', plain,
% 27.13/27.34      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 27.13/27.34         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 27.13/27.34          | ~ (v1_funct_1 @ X47)
% 27.13/27.34          | (m1_subset_1 @ (k2_partfun1 @ X48 @ X49 @ X47 @ X50) @ 
% 27.13/27.34             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 27.13/27.34      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 27.13/27.34  thf('30', plain,
% 27.13/27.34      (![X0 : $i]:
% 27.13/27.34         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 27.13/27.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))
% 27.13/27.34          | ~ (v1_funct_1 @ sk_E))),
% 27.13/27.34      inference('sup-', [status(thm)], ['28', '29'])).
% 27.13/27.34  thf('31', plain, ((v1_funct_1 @ sk_E)),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.13/27.34  thf('32', plain,
% 27.13/27.34      (![X0 : $i]:
% 27.13/27.34         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 27.13/27.34          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 27.13/27.34      inference('demod', [status(thm)], ['30', '31'])).
% 27.13/27.34  thf('33', plain,
% 27.13/27.34      (![X0 : $i]:
% 27.13/27.34         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 27.13/27.34      inference('demod', [status(thm)], ['3', '4'])).
% 27.13/27.34  thf('34', plain,
% 27.13/27.34      (![X0 : $i]:
% 27.13/27.34         (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 27.13/27.34          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 27.13/27.34      inference('demod', [status(thm)], ['32', '33'])).
% 27.13/27.34  thf(cc1_relset_1, axiom,
% 27.13/27.34    (![A:$i,B:$i,C:$i]:
% 27.13/27.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 27.13/27.34       ( v1_relat_1 @ C ) ))).
% 27.13/27.34  thf('35', plain,
% 27.13/27.34      (![X23 : $i, X24 : $i, X25 : $i]:
% 27.13/27.34         ((v1_relat_1 @ X23)
% 27.13/27.34          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 27.13/27.34      inference('cnf', [status(esa)], [cc1_relset_1])).
% 27.13/27.34  thf('36', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 27.13/27.34      inference('sup-', [status(thm)], ['34', '35'])).
% 27.13/27.34  thf('37', plain, ((r1_tarski @ sk_B @ sk_A)),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.13/27.34  thf('38', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_D)),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.13/27.34  thf(d1_funct_2, axiom,
% 27.13/27.34    (![A:$i,B:$i,C:$i]:
% 27.13/27.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 27.13/27.34       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 27.13/27.34           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 27.13/27.34             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 27.13/27.34         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 27.13/27.34           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 27.13/27.34             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 27.13/27.34  thf(zf_stmt_1, axiom,
% 27.13/27.34    (![C:$i,B:$i,A:$i]:
% 27.13/27.34     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 27.13/27.34       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 27.13/27.34  thf('39', plain,
% 27.13/27.34      (![X41 : $i, X42 : $i, X43 : $i]:
% 27.13/27.34         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 27.13/27.34          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 27.13/27.34          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 27.13/27.34  thf('40', plain,
% 27.13/27.34      ((~ (zip_tseitin_1 @ sk_E @ sk_D @ sk_A)
% 27.13/27.34        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_D @ sk_E)))),
% 27.13/27.34      inference('sup-', [status(thm)], ['38', '39'])).
% 27.13/27.34  thf('41', plain,
% 27.13/27.34      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.13/27.34  thf(redefinition_k1_relset_1, axiom,
% 27.13/27.34    (![A:$i,B:$i,C:$i]:
% 27.13/27.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 27.13/27.34       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 27.13/27.34  thf('42', plain,
% 27.13/27.34      (![X29 : $i, X30 : $i, X31 : $i]:
% 27.13/27.34         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 27.13/27.34          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 27.13/27.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 27.13/27.34  thf('43', plain,
% 27.13/27.34      (((k1_relset_1 @ sk_A @ sk_D @ sk_E) = (k1_relat_1 @ sk_E))),
% 27.13/27.34      inference('sup-', [status(thm)], ['41', '42'])).
% 27.13/27.34  thf('44', plain,
% 27.13/27.34      ((~ (zip_tseitin_1 @ sk_E @ sk_D @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_E)))),
% 27.13/27.34      inference('demod', [status(thm)], ['40', '43'])).
% 27.13/27.34  thf(zf_stmt_2, axiom,
% 27.13/27.34    (![B:$i,A:$i]:
% 27.13/27.34     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 27.13/27.34       ( zip_tseitin_0 @ B @ A ) ))).
% 27.13/27.34  thf('45', plain,
% 27.13/27.34      (![X39 : $i, X40 : $i]:
% 27.13/27.34         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_2])).
% 27.13/27.34  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 27.13/27.34  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 27.13/27.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 27.13/27.34  thf('47', plain,
% 27.13/27.34      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 27.13/27.34      inference('sup+', [status(thm)], ['45', '46'])).
% 27.13/27.34  thf('48', plain,
% 27.13/27.34      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.13/27.34  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 27.13/27.34  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 27.13/27.34  thf(zf_stmt_5, axiom,
% 27.13/27.34    (![A:$i,B:$i,C:$i]:
% 27.13/27.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 27.13/27.34       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 27.13/27.34         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 27.13/27.34           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 27.13/27.34             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 27.13/27.34  thf('49', plain,
% 27.13/27.34      (![X44 : $i, X45 : $i, X46 : $i]:
% 27.13/27.34         (~ (zip_tseitin_0 @ X44 @ X45)
% 27.13/27.34          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 27.13/27.34          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_5])).
% 27.13/27.34  thf('50', plain,
% 27.13/27.34      (((zip_tseitin_1 @ sk_E @ sk_D @ sk_A) | ~ (zip_tseitin_0 @ sk_D @ sk_A))),
% 27.13/27.34      inference('sup-', [status(thm)], ['48', '49'])).
% 27.13/27.34  thf('51', plain,
% 27.13/27.34      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_E @ sk_D @ sk_A))),
% 27.13/27.34      inference('sup-', [status(thm)], ['47', '50'])).
% 27.13/27.34  thf('52', plain, (~ (v1_xboole_0 @ sk_D)),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.13/27.34  thf('53', plain, ((zip_tseitin_1 @ sk_E @ sk_D @ sk_A)),
% 27.13/27.34      inference('clc', [status(thm)], ['51', '52'])).
% 27.13/27.34  thf('54', plain, (((sk_A) = (k1_relat_1 @ sk_E))),
% 27.13/27.34      inference('demod', [status(thm)], ['44', '53'])).
% 27.13/27.34  thf(t91_relat_1, axiom,
% 27.13/27.34    (![A:$i,B:$i]:
% 27.13/27.34     ( ( v1_relat_1 @ B ) =>
% 27.13/27.34       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 27.13/27.34         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 27.13/27.34  thf('55', plain,
% 27.13/27.34      (![X21 : $i, X22 : $i]:
% 27.13/27.34         (~ (r1_tarski @ X21 @ (k1_relat_1 @ X22))
% 27.13/27.34          | ((k1_relat_1 @ (k7_relat_1 @ X22 @ X21)) = (X21))
% 27.13/27.34          | ~ (v1_relat_1 @ X22))),
% 27.13/27.34      inference('cnf', [status(esa)], [t91_relat_1])).
% 27.13/27.34  thf('56', plain,
% 27.13/27.34      (![X0 : $i]:
% 27.13/27.34         (~ (r1_tarski @ X0 @ sk_A)
% 27.13/27.34          | ~ (v1_relat_1 @ sk_E)
% 27.13/27.34          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 27.13/27.34      inference('sup-', [status(thm)], ['54', '55'])).
% 27.13/27.34  thf('57', plain,
% 27.13/27.34      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.13/27.34  thf(cc2_relat_1, axiom,
% 27.13/27.34    (![A:$i]:
% 27.13/27.34     ( ( v1_relat_1 @ A ) =>
% 27.13/27.34       ( ![B:$i]:
% 27.13/27.34         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 27.13/27.34  thf('58', plain,
% 27.13/27.34      (![X11 : $i, X12 : $i]:
% 27.13/27.34         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 27.13/27.34          | (v1_relat_1 @ X11)
% 27.13/27.34          | ~ (v1_relat_1 @ X12))),
% 27.13/27.34      inference('cnf', [status(esa)], [cc2_relat_1])).
% 27.13/27.34  thf('59', plain,
% 27.13/27.34      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)) | (v1_relat_1 @ sk_E))),
% 27.13/27.34      inference('sup-', [status(thm)], ['57', '58'])).
% 27.13/27.34  thf(fc6_relat_1, axiom,
% 27.13/27.34    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 27.13/27.34  thf('60', plain,
% 27.13/27.34      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 27.13/27.34      inference('cnf', [status(esa)], [fc6_relat_1])).
% 27.13/27.34  thf('61', plain, ((v1_relat_1 @ sk_E)),
% 27.13/27.34      inference('demod', [status(thm)], ['59', '60'])).
% 27.13/27.34  thf('62', plain,
% 27.13/27.34      (![X0 : $i]:
% 27.13/27.34         (~ (r1_tarski @ X0 @ sk_A)
% 27.13/27.34          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 27.13/27.34      inference('demod', [status(thm)], ['56', '61'])).
% 27.13/27.34  thf('63', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 27.13/27.34      inference('sup-', [status(thm)], ['37', '62'])).
% 27.13/27.34  thf('64', plain, ((v1_relat_1 @ sk_E)),
% 27.13/27.34      inference('demod', [status(thm)], ['59', '60'])).
% 27.13/27.34  thf('65', plain,
% 27.13/27.34      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 27.13/27.34        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 27.13/27.34      inference('demod', [status(thm)], ['27', '36', '63', '64'])).
% 27.13/27.34  thf('66', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)),
% 27.13/27.34      inference('demod', [status(thm)], ['15', '65'])).
% 27.13/27.34  thf('67', plain,
% 27.13/27.34      (![X39 : $i, X40 : $i]:
% 27.13/27.34         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_2])).
% 27.13/27.34  thf('68', plain,
% 27.13/27.34      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 27.13/27.34        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 27.13/27.34      inference('demod', [status(thm)], ['27', '36', '63', '64'])).
% 27.13/27.34  thf('69', plain,
% 27.13/27.34      (![X44 : $i, X45 : $i, X46 : $i]:
% 27.13/27.34         (~ (zip_tseitin_0 @ X44 @ X45)
% 27.13/27.34          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 27.13/27.34          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_5])).
% 27.13/27.34  thf('70', plain,
% 27.13/27.34      (((zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)
% 27.13/27.34        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 27.13/27.34      inference('sup-', [status(thm)], ['68', '69'])).
% 27.13/27.34  thf('71', plain,
% 27.13/27.34      ((((sk_C) = (k1_xboole_0))
% 27.13/27.34        | (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B))),
% 27.13/27.34      inference('sup-', [status(thm)], ['67', '70'])).
% 27.13/27.34  thf('72', plain,
% 27.13/27.34      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 27.13/27.34        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 27.13/27.34      inference('demod', [status(thm)], ['27', '36', '63', '64'])).
% 27.13/27.34  thf('73', plain,
% 27.13/27.34      (![X29 : $i, X30 : $i, X31 : $i]:
% 27.13/27.34         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 27.13/27.34          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 27.13/27.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 27.13/27.34  thf('74', plain,
% 27.13/27.34      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B))
% 27.13/27.34         = (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 27.13/27.34      inference('sup-', [status(thm)], ['72', '73'])).
% 27.13/27.34  thf('75', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 27.13/27.34      inference('sup-', [status(thm)], ['37', '62'])).
% 27.13/27.34  thf('76', plain,
% 27.13/27.34      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 27.13/27.34      inference('demod', [status(thm)], ['74', '75'])).
% 27.13/27.34  thf('77', plain,
% 27.13/27.34      (![X41 : $i, X42 : $i, X43 : $i]:
% 27.13/27.34         (((X41) != (k1_relset_1 @ X41 @ X42 @ X43))
% 27.13/27.34          | (v1_funct_2 @ X43 @ X41 @ X42)
% 27.13/27.34          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 27.13/27.34  thf('78', plain,
% 27.13/27.34      ((((sk_B) != (sk_B))
% 27.13/27.34        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)
% 27.13/27.34        | (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C))),
% 27.13/27.34      inference('sup-', [status(thm)], ['76', '77'])).
% 27.13/27.34  thf('79', plain,
% 27.13/27.34      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 27.13/27.34        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B))),
% 27.13/27.34      inference('simplify', [status(thm)], ['78'])).
% 27.13/27.34  thf('80', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)),
% 27.13/27.34      inference('demod', [status(thm)], ['15', '65'])).
% 27.13/27.34  thf('81', plain,
% 27.13/27.34      (~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)),
% 27.13/27.34      inference('clc', [status(thm)], ['79', '80'])).
% 27.13/27.34  thf('82', plain, (((sk_C) = (k1_xboole_0))),
% 27.13/27.34      inference('sup-', [status(thm)], ['71', '81'])).
% 27.13/27.34  thf('83', plain,
% 27.13/27.34      (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ k1_xboole_0)),
% 27.13/27.34      inference('demod', [status(thm)], ['66', '82'])).
% 27.13/27.34  thf('84', plain,
% 27.13/27.34      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 27.13/27.34        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 27.13/27.34      inference('demod', [status(thm)], ['27', '36', '63', '64'])).
% 27.13/27.34  thf(t3_subset, axiom,
% 27.13/27.34    (![A:$i,B:$i]:
% 27.13/27.34     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 27.13/27.34  thf('85', plain,
% 27.13/27.34      (![X8 : $i, X9 : $i]:
% 27.13/27.34         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 27.13/27.34      inference('cnf', [status(esa)], [t3_subset])).
% 27.13/27.34  thf('86', plain,
% 27.13/27.34      ((r1_tarski @ (k7_relat_1 @ sk_E @ sk_B) @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 27.13/27.34      inference('sup-', [status(thm)], ['84', '85'])).
% 27.13/27.34  thf('87', plain,
% 27.13/27.34      (![X0 : $i, X2 : $i]:
% 27.13/27.34         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 27.13/27.34      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.13/27.34  thf('88', plain,
% 27.13/27.34      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_B @ sk_C) @ (k7_relat_1 @ sk_E @ sk_B))
% 27.13/27.34        | ((k2_zfmisc_1 @ sk_B @ sk_C) = (k7_relat_1 @ sk_E @ sk_B)))),
% 27.13/27.34      inference('sup-', [status(thm)], ['86', '87'])).
% 27.13/27.34  thf('89', plain, (((sk_C) = (k1_xboole_0))),
% 27.13/27.34      inference('sup-', [status(thm)], ['71', '81'])).
% 27.13/27.34  thf(t113_zfmisc_1, axiom,
% 27.13/27.34    (![A:$i,B:$i]:
% 27.13/27.34     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 27.13/27.34       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 27.13/27.34  thf('90', plain,
% 27.13/27.34      (![X6 : $i, X7 : $i]:
% 27.13/27.34         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 27.13/27.34      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 27.13/27.34  thf('91', plain,
% 27.13/27.34      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 27.13/27.34      inference('simplify', [status(thm)], ['90'])).
% 27.13/27.34  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 27.13/27.34  thf('92', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 27.13/27.34      inference('cnf', [status(esa)], [t2_xboole_1])).
% 27.13/27.34  thf('93', plain, (((sk_C) = (k1_xboole_0))),
% 27.13/27.34      inference('sup-', [status(thm)], ['71', '81'])).
% 27.13/27.34  thf('94', plain,
% 27.13/27.34      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 27.13/27.34      inference('simplify', [status(thm)], ['90'])).
% 27.13/27.34  thf('95', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_E @ sk_B))),
% 27.13/27.34      inference('demod', [status(thm)], ['88', '89', '91', '92', '93', '94'])).
% 27.13/27.34  thf('96', plain, (~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ k1_xboole_0)),
% 27.13/27.34      inference('demod', [status(thm)], ['83', '95'])).
% 27.13/27.34  thf('97', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 27.13/27.34      inference('sup-', [status(thm)], ['37', '62'])).
% 27.13/27.34  thf('98', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 27.13/27.34      inference('simplify', [status(thm)], ['22'])).
% 27.13/27.34  thf('99', plain,
% 27.13/27.34      (![X0 : $i, X1 : $i]:
% 27.13/27.34         (~ (v1_relat_1 @ X0)
% 27.13/27.34          | (m1_subset_1 @ X0 @ 
% 27.13/27.34             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 27.13/27.34          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 27.13/27.34      inference('sup-', [status(thm)], ['23', '24'])).
% 27.13/27.34  thf('100', plain,
% 27.13/27.34      (![X0 : $i]:
% 27.13/27.34         ((m1_subset_1 @ X0 @ 
% 27.13/27.34           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 27.13/27.34          | ~ (v1_relat_1 @ X0))),
% 27.13/27.34      inference('sup-', [status(thm)], ['98', '99'])).
% 27.13/27.34  thf('101', plain,
% 27.13/27.34      (![X29 : $i, X30 : $i, X31 : $i]:
% 27.13/27.34         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 27.13/27.34          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 27.13/27.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 27.13/27.34  thf('102', plain,
% 27.13/27.34      (![X0 : $i]:
% 27.13/27.34         (~ (v1_relat_1 @ X0)
% 27.13/27.34          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 27.13/27.34              = (k1_relat_1 @ X0)))),
% 27.13/27.34      inference('sup-', [status(thm)], ['100', '101'])).
% 27.13/27.34  thf('103', plain,
% 27.13/27.34      ((((k1_relset_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ 
% 27.13/27.34          (k7_relat_1 @ sk_E @ sk_B))
% 27.13/27.34          = (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))
% 27.13/27.34        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 27.13/27.34      inference('sup+', [status(thm)], ['97', '102'])).
% 27.13/27.34  thf('104', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 27.13/27.34      inference('sup-', [status(thm)], ['37', '62'])).
% 27.13/27.34  thf('105', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 27.13/27.34      inference('sup-', [status(thm)], ['34', '35'])).
% 27.13/27.34  thf('106', plain,
% 27.13/27.34      (((k1_relset_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ 
% 27.13/27.34         (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 27.13/27.34      inference('demod', [status(thm)], ['103', '104', '105'])).
% 27.13/27.34  thf('107', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_E @ sk_B))),
% 27.13/27.34      inference('demod', [status(thm)], ['88', '89', '91', '92', '93', '94'])).
% 27.13/27.34  thf('108', plain, (((k1_xboole_0) = (k7_relat_1 @ sk_E @ sk_B))),
% 27.13/27.34      inference('demod', [status(thm)], ['88', '89', '91', '92', '93', '94'])).
% 27.13/27.34  thf('109', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 27.13/27.34      inference('cnf', [status(esa)], [t2_xboole_1])).
% 27.13/27.34  thf('110', plain,
% 27.13/27.34      (![X8 : $i, X10 : $i]:
% 27.13/27.34         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 27.13/27.34      inference('cnf', [status(esa)], [t3_subset])).
% 27.13/27.34  thf('111', plain,
% 27.13/27.34      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 27.13/27.34      inference('sup-', [status(thm)], ['109', '110'])).
% 27.13/27.34  thf('112', plain,
% 27.13/27.34      (![X29 : $i, X30 : $i, X31 : $i]:
% 27.13/27.34         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 27.13/27.34          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 27.13/27.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 27.13/27.34  thf('113', plain,
% 27.13/27.34      (![X0 : $i, X1 : $i]:
% 27.13/27.34         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 27.13/27.34      inference('sup-', [status(thm)], ['111', '112'])).
% 27.13/27.34  thf('114', plain,
% 27.13/27.34      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 27.13/27.34      inference('sup-', [status(thm)], ['109', '110'])).
% 27.13/27.34  thf(cc2_relset_1, axiom,
% 27.13/27.34    (![A:$i,B:$i,C:$i]:
% 27.13/27.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 27.13/27.34       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 27.13/27.34  thf('115', plain,
% 27.13/27.34      (![X26 : $i, X27 : $i, X28 : $i]:
% 27.13/27.34         ((v4_relat_1 @ X26 @ X27)
% 27.13/27.34          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 27.13/27.34      inference('cnf', [status(esa)], [cc2_relset_1])).
% 27.13/27.34  thf('116', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 27.13/27.34      inference('sup-', [status(thm)], ['114', '115'])).
% 27.13/27.34  thf(d18_relat_1, axiom,
% 27.13/27.34    (![A:$i,B:$i]:
% 27.13/27.34     ( ( v1_relat_1 @ B ) =>
% 27.13/27.34       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 27.13/27.34  thf('117', plain,
% 27.13/27.34      (![X13 : $i, X14 : $i]:
% 27.13/27.34         (~ (v4_relat_1 @ X13 @ X14)
% 27.13/27.34          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 27.13/27.34          | ~ (v1_relat_1 @ X13))),
% 27.13/27.34      inference('cnf', [status(esa)], [d18_relat_1])).
% 27.13/27.34  thf('118', plain,
% 27.13/27.34      (![X0 : $i]:
% 27.13/27.34         (~ (v1_relat_1 @ k1_xboole_0)
% 27.13/27.34          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 27.13/27.34      inference('sup-', [status(thm)], ['116', '117'])).
% 27.13/27.34  thf('119', plain,
% 27.13/27.34      (![X6 : $i, X7 : $i]:
% 27.13/27.34         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 27.13/27.34      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 27.13/27.34  thf('120', plain,
% 27.13/27.34      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 27.13/27.34      inference('simplify', [status(thm)], ['119'])).
% 27.13/27.34  thf('121', plain,
% 27.13/27.34      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 27.13/27.34      inference('cnf', [status(esa)], [fc6_relat_1])).
% 27.13/27.34  thf('122', plain, ((v1_relat_1 @ k1_xboole_0)),
% 27.13/27.34      inference('sup+', [status(thm)], ['120', '121'])).
% 27.13/27.34  thf('123', plain,
% 27.13/27.34      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 27.13/27.34      inference('demod', [status(thm)], ['118', '122'])).
% 27.13/27.34  thf(t3_xboole_1, axiom,
% 27.13/27.34    (![A:$i]:
% 27.13/27.34     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 27.13/27.34  thf('124', plain,
% 27.13/27.34      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 27.13/27.34      inference('cnf', [status(esa)], [t3_xboole_1])).
% 27.13/27.34  thf('125', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 27.13/27.34      inference('sup-', [status(thm)], ['123', '124'])).
% 27.13/27.34  thf('126', plain,
% 27.13/27.34      (![X0 : $i, X1 : $i]:
% 27.13/27.34         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 27.13/27.34      inference('demod', [status(thm)], ['113', '125'])).
% 27.13/27.34  thf('127', plain, (((k1_xboole_0) = (sk_B))),
% 27.13/27.34      inference('demod', [status(thm)], ['106', '107', '108', '126'])).
% 27.13/27.34  thf('128', plain,
% 27.13/27.34      (![X0 : $i, X1 : $i]:
% 27.13/27.34         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 27.13/27.34      inference('demod', [status(thm)], ['113', '125'])).
% 27.13/27.34  thf('129', plain,
% 27.13/27.34      (![X41 : $i, X42 : $i, X43 : $i]:
% 27.13/27.34         (((X41) != (k1_relset_1 @ X41 @ X42 @ X43))
% 27.13/27.34          | (v1_funct_2 @ X43 @ X41 @ X42)
% 27.13/27.34          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_1])).
% 27.13/27.34  thf('130', plain,
% 27.13/27.34      (![X0 : $i, X1 : $i]:
% 27.13/27.34         (((X1) != (k1_xboole_0))
% 27.13/27.34          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 27.13/27.34          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 27.13/27.34      inference('sup-', [status(thm)], ['128', '129'])).
% 27.13/27.34  thf('131', plain,
% 27.13/27.34      (![X0 : $i]:
% 27.13/27.34         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 27.13/27.34          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 27.13/27.34      inference('simplify', [status(thm)], ['130'])).
% 27.13/27.34  thf('132', plain,
% 27.13/27.34      (![X39 : $i, X40 : $i]:
% 27.13/27.34         ((zip_tseitin_0 @ X39 @ X40) | ((X40) != (k1_xboole_0)))),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_2])).
% 27.13/27.34  thf('133', plain, (![X39 : $i]: (zip_tseitin_0 @ X39 @ k1_xboole_0)),
% 27.13/27.34      inference('simplify', [status(thm)], ['132'])).
% 27.13/27.34  thf('134', plain,
% 27.13/27.34      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 27.13/27.34      inference('sup-', [status(thm)], ['109', '110'])).
% 27.13/27.34  thf('135', plain,
% 27.13/27.34      (![X44 : $i, X45 : $i, X46 : $i]:
% 27.13/27.34         (~ (zip_tseitin_0 @ X44 @ X45)
% 27.13/27.34          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 27.13/27.34          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 27.13/27.34      inference('cnf', [status(esa)], [zf_stmt_5])).
% 27.13/27.34  thf('136', plain,
% 27.13/27.34      (![X0 : $i, X1 : $i]:
% 27.13/27.34         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 27.13/27.34      inference('sup-', [status(thm)], ['134', '135'])).
% 27.13/27.34  thf('137', plain,
% 27.13/27.34      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 27.13/27.34      inference('sup-', [status(thm)], ['133', '136'])).
% 27.13/27.34  thf('138', plain,
% 27.13/27.34      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 27.13/27.34      inference('demod', [status(thm)], ['131', '137'])).
% 27.13/27.34  thf('139', plain, ($false),
% 27.13/27.34      inference('demod', [status(thm)], ['96', '127', '138'])).
% 27.13/27.34  
% 27.13/27.34  % SZS output end Refutation
% 27.13/27.34  
% 27.13/27.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
